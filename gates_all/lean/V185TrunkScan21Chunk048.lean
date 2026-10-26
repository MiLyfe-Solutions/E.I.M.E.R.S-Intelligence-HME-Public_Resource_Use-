import V185TrunkScan21Chunk047

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_581072 : List Nat := [2, 1, 1, 1, 1, 2, 2, 7, 4]
def baseStart_581072 : Nat := 118140960795 + 581072 * 2 ^ 59
def prefixEnd_581072 : Nat := 4983230072969 + 3 ^ 40 * 581072 * 2
def baseEnd_581072 : Nat := 132608547053091460812313

theorem tailTrace_581072 : CollatzResearch.WordTrace tailWord_581072 prefixEnd_581072 132608547053091460812313 := by
  unfold tailWord_581072
  simp only [CollatzResearch.WordTrace]
  refine ⟨10596718475441429020936735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14128957967255238694582313 10596718475441429020936735)
  ·
    refine ⟨15895077713162143531405103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10596718475441429020936735 15895077713162143531405103)
    ·
      refine ⟨23842616569743215297107655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15895077713162143531405103 23842616569743215297107655)
      ·
        refine ⟨35763924854614822945661483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23842616569743215297107655 35763924854614822945661483)
        ·
          refine ⟨53645887281922234418492225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35763924854614822945661483 53645887281922234418492225)
          ·
            refine ⟨40234415461441675813869169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53645887281922234418492225 40234415461441675813869169)
            ·
              refine ⟨30175811596081256860401877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40234415461441675813869169 30175811596081256860401877)
              ·
                refine ⟨707245584283154457665669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 30175811596081256860401877 707245584283154457665669)
                ·
                  refine ⟨132608547053091460812313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 707245584283154457665669 132608547053091460812313)
                  ·
                    rfl

theorem cell21_581072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 7, 4].length) (baseStart_581072 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_581072 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_581072 prefixEnd_581072 := by exact prefixLift 581072
  have htrace : WordTrace (prefixWord ++ tailWord_581072) baseStart_581072 baseEnd_581072 := by
    simpa [prefixWord, tailWord_581072, baseEnd_581072] using wordTrace_append hprefix tailTrace_581072
  have hstable : (prefixWord ++ tailWord_581072).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581072).length < 2 ^ (prefixWord ++ tailWord_581072).sum := by decide
  have hdescent : baseEnd_581072 < baseStart_581072 := by decide
  rcases family_descends (prefixWord ++ tailWord_581072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581106 : List Nat := [3, 2, 1, 4, 1, 2, 2, 2, 4]
def baseStart_581106 : Nat := 118140960795 + 581106 * 2 ^ 59
def prefixEnd_581106 : Nat := 4983230072969 + 3 ^ 40 * 581106 * 2
def baseEnd_581106 : Nat := 132616306316314957245577

theorem tailTrace_581106 : CollatzResearch.WordTrace tailWord_581106 prefixEnd_581106 132616306316314957245577 := by
  unfold tailWord_581106
  simp only [CollatzResearch.WordTrace]
  refine ⟨5298669258189920462152793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14129784688506454565740781 5298669258189920462152793)
  ·
    refine ⟨3974001943642440346614595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5298669258189920462152793 3974001943642440346614595)
    ·
      refine ⟨5961002915463660519921893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3974001943642440346614595 5961002915463660519921893)
      ·
        refine ⟨1117688046649436347485355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5961002915463660519921893 1117688046649436347485355)
        ·
          refine ⟨1676532069974154521228033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1117688046649436347485355 1676532069974154521228033)
          ·
            refine ⟨1257399052480615890921025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1676532069974154521228033 1257399052480615890921025)
            ·
              refine ⟨943049289360461918190769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1257399052480615890921025 943049289360461918190769)
              ·
                refine ⟨707286967020346438643077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 943049289360461918190769 707286967020346438643077)
                ·
                  refine ⟨132616306316314957245577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 707286967020346438643077 132616306316314957245577)
                  ·
                    rfl

theorem cell21_581106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_581106 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_581106 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_581106 prefixEnd_581106 := by exact prefixLift 581106
  have htrace : WordTrace (prefixWord ++ tailWord_581106) baseStart_581106 baseEnd_581106 := by
    simpa [prefixWord, tailWord_581106, baseEnd_581106] using wordTrace_append hprefix tailTrace_581106
  have hstable : (prefixWord ++ tailWord_581106).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581106).length < 2 ^ (prefixWord ++ tailWord_581106).sum := by decide
  have hdescent : baseEnd_581106 < baseStart_581106 := by decide
  rcases family_descends (prefixWord ++ tailWord_581106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581109 : List Nat := [1, 3, 5, 1, 1, 1, 4, 2, 3]
def baseStart_581109 : Nat := 118140960795 + 581109 * 2 ^ 59
def prefixEnd_581109 : Nat := 4983230072969 + 3 ^ 40 * 581109 * 2
def baseEnd_581109 : Nat := 132616990957187618695571

theorem tailTrace_581109 : CollatzResearch.WordTrace tailWord_581109 prefixEnd_581109 132616990957187618695571 := by
  unfold tailWord_581109
  simp only [CollatzResearch.WordTrace]
  refine ⟨21194786451748813360970381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14129857634499208907313587 21194786451748813360970381)
  ·
    refine ⟨7948044919405805010363893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21194786451748813360970381 7948044919405805010363893)
    ·
      refine ⟨745129211194294219721615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7948044919405805010363893 745129211194294219721615)
      ·
        refine ⟨1117693816791441329582423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 745129211194294219721615 1117693816791441329582423)
        ·
          refine ⟨1676540725187161994373635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1117693816791441329582423 1676540725187161994373635)
          ·
            refine ⟨2514811087780742991560453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1676540725187161994373635 2514811087780742991560453)
            ·
              refine ⟨471527078958889310917585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2514811087780742991560453 471527078958889310917585)
              ·
                refine ⟨353645309219166983188189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 471527078958889310917585 353645309219166983188189)
                ·
                  refine ⟨132616990957187618695571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 353645309219166983188189 132616990957187618695571)
                  ·
                    rfl

theorem cell21_581109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 2, 3].length) (baseStart_581109 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_581109 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_581109 prefixEnd_581109 := by exact prefixLift 581109
  have htrace : WordTrace (prefixWord ++ tailWord_581109) baseStart_581109 baseEnd_581109 := by
    simpa [prefixWord, tailWord_581109, baseEnd_581109] using wordTrace_append hprefix tailTrace_581109
  have hstable : (prefixWord ++ tailWord_581109).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581109).length < 2 ^ (prefixWord ++ tailWord_581109).sum := by decide
  have hdescent : baseEnd_581109 < baseStart_581109 := by decide
  rcases family_descends (prefixWord ++ tailWord_581109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581148 : List Nat := [2, 2, 3, 1, 2, 1, 2, 2, 6]
def baseStart_581148 : Nat := 118140960795 + 581148 * 2 ^ 59
def prefixEnd_581148 : Nat := 4983230072969 + 3 ^ 40 * 581148 * 2
def baseEnd_581148 : Nat := 132625891288532217545491

theorem tailTrace_581148 : CollatzResearch.WordTrace tailWord_581148 prefixEnd_581148 132625891288532217545491 := by
  unfold tailWord_581148
  simp only [CollatzResearch.WordTrace]
  refine ⟨10598104449303761510820049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14130805932405015347760065 10598104449303761510820049)
  ·
    refine ⟨7948578336977821133115037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10598104449303761510820049 7948578336977821133115037)
    ·
      refine ⟨2980716876366682924918139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7948578336977821133115037 2980716876366682924918139)
      ·
        refine ⟨4471075314550024387377209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2980716876366682924918139 4471075314550024387377209)
        ·
          refine ⟨3353306485912518290532907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4471075314550024387377209 3353306485912518290532907)
          ·
            refine ⟨5029959728868777435799361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3353306485912518290532907 5029959728868777435799361)
            ·
              refine ⟨3772469796651583076849521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5029959728868777435799361 3772469796651583076849521)
              ·
                refine ⟨2829352347488687307637141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3772469796651583076849521 2829352347488687307637141)
                ·
                  refine ⟨132625891288532217545491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2829352347488687307637141 132625891288532217545491)
                  ·
                    rfl

theorem cell21_581148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 6].length) (baseStart_581148 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_581148 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_581148 prefixEnd_581148 := by exact prefixLift 581148
  have htrace : WordTrace (prefixWord ++ tailWord_581148) baseStart_581148 baseEnd_581148 := by
    simpa [prefixWord, tailWord_581148, baseEnd_581148] using wordTrace_append hprefix tailTrace_581148
  have hstable : (prefixWord ++ tailWord_581148).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581148).length < 2 ^ (prefixWord ++ tailWord_581148).sum := by decide
  have hdescent : baseEnd_581148 < baseStart_581148 := by decide
  rcases family_descends (prefixWord ++ tailWord_581148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581196 : List Nat := [2, 2, 1, 3, 1, 5, 2, 5]
def baseStart_581196 : Nat := 118140960795 + 581196 * 2 ^ 59
def prefixEnd_581196 : Nat := 4983230072969 + 3 ^ 40 * 581196 * 2
def baseEnd_581196 : Nat := 44212281847498266915131

theorem tailTrace_581196 : CollatzResearch.WordTrace tailWord_581196 prefixEnd_581196 44212281847498266915131 := by
  unfold tailWord_581196
  simp only [CollatzResearch.WordTrace]
  refine ⟨10598979801216813609693721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14131973068289084812924961 10598979801216813609693721)
  ·
    refine ⟨7949234850912610207270291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10598979801216813609693721 7949234850912610207270291)
    ·
      refine ⟨11923852276368915310905437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7949234850912610207270291 11923852276368915310905437)
      ·
        refine ⟨4471444603638343241589539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11923852276368915310905437 4471444603638343241589539)
        ·
          refine ⟨6707166905457514862384309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4471444603638343241589539 6707166905457514862384309)
          ·
            refine ⟨628796897386642018348529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6707166905457514862384309 628796897386642018348529)
            ·
              refine ⟨471597673039981513761397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 628796897386642018348529 471597673039981513761397)
              ·
                refine ⟨44212281847498266915131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 471597673039981513761397 44212281847498266915131)
                ·
                  rfl

theorem cell21_581196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 5].length) (baseStart_581196 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_581196 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_581196 prefixEnd_581196 := by exact prefixLift 581196
  have htrace : WordTrace (prefixWord ++ tailWord_581196) baseStart_581196 baseEnd_581196 := by
    simpa [prefixWord, tailWord_581196, baseEnd_581196] using wordTrace_append hprefix tailTrace_581196
  have hstable : (prefixWord ++ tailWord_581196).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581196).length < 2 ^ (prefixWord ++ tailWord_581196).sum := by decide
  have hdescent : baseEnd_581196 < baseStart_581196 := by decide
  rcases family_descends (prefixWord ++ tailWord_581196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581213 : List Nat := [1, 4, 4, 2, 1, 2, 7]
def baseStart_581213 : Nat := 118140960795 + 581213 * 2 ^ 59
def prefixEnd_581213 : Nat := 4983230072969 + 3 ^ 40 * 581213 * 2
def baseEnd_581213 : Nat := 14737858352678505440225

theorem tailTrace_581213 : CollatzResearch.WordTrace tailWord_581213 prefixEnd_581213 14737858352678505440225 := by
  unfold tailWord_581213
  simp only [CollatzResearch.WordTrace]
  refine ⟨21198579643372039122756293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14132386428914692748504195 21198579643372039122756293)
  ·
    refine ⟨3974733683132257335516805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21198579643372039122756293 3974733683132257335516805)
    ·
      refine ⟨745262565587298250409401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3974733683132257335516805 745262565587298250409401)
      ·
        refine ⟨558946924190473687807051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 745262565587298250409401 558946924190473687807051)
        ·
          refine ⟨838420386285710531710577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 558946924190473687807051 838420386285710531710577)
          ·
            refine ⟨628815289714282898782933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 838420386285710531710577 628815289714282898782933)
            ·
              refine ⟨14737858352678505440225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 628815289714282898782933 14737858352678505440225)
              ·
                rfl

theorem cell21_581213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 7].length) (baseStart_581213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_581213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_581213 prefixEnd_581213 := by exact prefixLift 581213
  have htrace : WordTrace (prefixWord ++ tailWord_581213) baseStart_581213 baseEnd_581213 := by
    simpa [prefixWord, tailWord_581213, baseEnd_581213] using wordTrace_append hprefix tailTrace_581213
  have hstable : (prefixWord ++ tailWord_581213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581213).length < 2 ^ (prefixWord ++ tailWord_581213).sum := by decide
  have hdescent : baseEnd_581213 < baseStart_581213 := by decide
  rcases family_descends (prefixWord ++ tailWord_581213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581351 : List Nat := [1, 1, 5, 4, 1, 1, 3, 1, 4]
def baseStart_581351 : Nat := 118140960795 + 581351 * 2 ^ 59
def prefixEnd_581351 : Nat := 4983230072969 + 3 ^ 40 * 581351 * 2
def baseEnd_581351 : Nat := 132672218654248975661743

theorem tailTrace_581351 : CollatzResearch.WordTrace tailWord_581351 prefixEnd_581351 132672218654248975661743 := by
  unfold tailWord_581351
  simp only [CollatzResearch.WordTrace]
  refine ⟨21203612916872088691279907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14135741944581392460853271 21203612916872088691279907)
  ·
    refine ⟨31805419375308133036919861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21203612916872088691279907 31805419375308133036919861)
    ·
      refine ⟨2981758066435137472211237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31805419375308133036919861 2981758066435137472211237)
      ·
        refine ⟨559079637456588276039607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2981758066435137472211237 559079637456588276039607)
        ·
          refine ⟨838619456184882414059411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 559079637456588276039607 838619456184882414059411)
          ·
            refine ⟨1257929184277323621089117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 838619456184882414059411 1257929184277323621089117)
            ·
              refine ⟨471723444103996357908419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1257929184277323621089117 471723444103996357908419)
              ·
                refine ⟨707585166155994536862629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 471723444103996357908419 707585166155994536862629)
                ·
                  refine ⟨132672218654248975661743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 707585166155994536862629 132672218654248975661743)
                  ·
                    rfl

theorem cell21_581351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 1, 4].length) (baseStart_581351 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_581351 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_581351 prefixEnd_581351 := by exact prefixLift 581351
  have htrace : WordTrace (prefixWord ++ tailWord_581351) baseStart_581351 baseEnd_581351 := by
    simpa [prefixWord, tailWord_581351, baseEnd_581351] using wordTrace_append hprefix tailTrace_581351
  have hstable : (prefixWord ++ tailWord_581351).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581351).length < 2 ^ (prefixWord ++ tailWord_581351).sum := by decide
  have hdescent : baseEnd_581351 < baseStart_581351 := by decide
  rcases family_descends (prefixWord ++ tailWord_581351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581390 : List Nat := [4, 1, 1, 2, 1, 1, 11]
def baseStart_581390 : Nat := 118140960795 + 581390 * 2 ^ 59
def prefixEnd_581390 : Nat := 4983230072969 + 3 ^ 40 * 581390 * 2
def baseEnd_581390 : Nat := 14742346553954841612407

theorem tailTrace_581390 : CollatzResearch.WordTrace tailWord_581390 prefixEnd_581390 14742346553954841612407 := by
  unfold tailWord_581390
  simp only [CollatzResearch.WordTrace]
  refine ⟨2650629420466349793993703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14136690242487198901299749 2650629420466349793993703)
  ·
    refine ⟨3975944130699524690990555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2650629420466349793993703 3975944130699524690990555)
    ·
      refine ⟨5963916196049287036485833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3975944130699524690990555 5963916196049287036485833)
      ·
        refine ⟨4472937147036965277364375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5963916196049287036485833 4472937147036965277364375)
        ·
          refine ⟨6709405720555447916046563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4472937147036965277364375 6709405720555447916046563)
          ·
            refine ⟨10064108580833171874069845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6709405720555447916046563 10064108580833171874069845)
            ·
              refine ⟨14742346553954841612407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 10064108580833171874069845 14742346553954841612407)
              ·
                rfl

theorem cell21_581390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 11].length) (baseStart_581390 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_581390 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_581390 prefixEnd_581390 := by exact prefixLift 581390
  have htrace : WordTrace (prefixWord ++ tailWord_581390) baseStart_581390 baseEnd_581390 := by
    simpa [prefixWord, tailWord_581390, baseEnd_581390] using wordTrace_append hprefix tailTrace_581390
  have hstable : (prefixWord ++ tailWord_581390).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581390).length < 2 ^ (prefixWord ++ tailWord_581390).sum := by decide
  have hdescent : baseEnd_581390 < baseStart_581390 := by decide
  rcases family_descends (prefixWord ++ tailWord_581390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581534 : List Nat := [4, 3, 1, 3, 1, 2, 2, 5]
def baseStart_581534 : Nat := 118140960795 + 581534 * 2 ^ 59
def prefixEnd_581534 : Nat := 4983230072969 + 3 ^ 40 * 581534 * 2
def baseEnd_581534 : Nat := 44237993915827108037123

theorem tailTrace_581534 : CollatzResearch.WordTrace tailWord_581534 prefixEnd_581534 44237993915827108037123 := by
  unfold tailWord_581534
  simp only [CollatzResearch.WordTrace]
  refine ⟨2651285934401138868148957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14140191650139407296794437 2651285934401138868148957)
  ·
    refine ⟨994232225400427075555859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2651285934401138868148957 994232225400427075555859)
    ·
      refine ⟨1491348338100640613333789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 994232225400427075555859 1491348338100640613333789)
      ·
        refine ⟨559255626787740230000171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1491348338100640613333789 559255626787740230000171)
        ·
          refine ⟨838883440181610345000257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 559255626787740230000171 838883440181610345000257)
          ·
            refine ⟨629162580136207758750193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 838883440181610345000257 629162580136207758750193)
            ·
              refine ⟨471871935102155819062645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 629162580136207758750193 471871935102155819062645)
              ·
                refine ⟨44237993915827108037123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 471871935102155819062645 44237993915827108037123)
                ·
                  rfl

theorem cell21_581534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 5].length) (baseStart_581534 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_581534 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_581534 prefixEnd_581534 := by exact prefixLift 581534
  have htrace : WordTrace (prefixWord ++ tailWord_581534) baseStart_581534 baseEnd_581534 := by
    simpa [prefixWord, tailWord_581534, baseEnd_581534] using wordTrace_append hprefix tailTrace_581534
  have hstable : (prefixWord ++ tailWord_581534).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581534).length < 2 ^ (prefixWord ++ tailWord_581534).sum := by decide
  have hdescent : baseEnd_581534 < baseStart_581534 := by decide
  rcases family_descends (prefixWord ++ tailWord_581534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581663 : List Nat := [1, 1, 2, 4, 1, 2, 2, 2, 6]
def baseStart_581663 : Nat := 118140960795 + 581663 * 2 ^ 59
def prefixEnd_581663 : Nat := 4983230072969 + 3 ^ 40 * 581663 * 2
def baseEnd_581663 : Nat := 132743421305005766461105

theorem tailTrace_581663 : CollatzResearch.WordTrace tailWord_581663 prefixEnd_581663 132743421305005766461105 := by
  unfold tailWord_581663
  simp only [CollatzResearch.WordTrace]
  refine ⟨21214992491741765976637643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14143328327827843984425095 21214992491741765976637643)
  ·
    refine ⟨31822488737612648964956465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21214992491741765976637643 31822488737612648964956465)
    ·
      refine ⟨23866866553209486723717349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31822488737612648964956465 23866866553209486723717349)
      ·
        refine ⟨4475037478726778760697003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23866866553209486723717349 4475037478726778760697003)
        ·
          refine ⟨6712556218090168141045505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4475037478726778760697003 6712556218090168141045505)
          ·
            refine ⟨5034417163567626105784129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6712556218090168141045505 5034417163567626105784129)
            ·
              refine ⟨3775812872675719579338097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5034417163567626105784129 3775812872675719579338097)
              ·
                refine ⟨2831859654506789684503573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3775812872675719579338097 2831859654506789684503573)
                ·
                  refine ⟨132743421305005766461105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2831859654506789684503573 132743421305005766461105)
                  ·
                    rfl

theorem cell21_581663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 6].length) (baseStart_581663 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_581663 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_581663 prefixEnd_581663 := by exact prefixLift 581663
  have htrace : WordTrace (prefixWord ++ tailWord_581663) baseStart_581663 baseEnd_581663 := by
    simpa [prefixWord, tailWord_581663, baseEnd_581663] using wordTrace_append hprefix tailTrace_581663
  have hstable : (prefixWord ++ tailWord_581663).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581663).length < 2 ^ (prefixWord ++ tailWord_581663).sum := by decide
  have hdescent : baseEnd_581663 < baseStart_581663 := by decide
  rcases family_descends (prefixWord ++ tailWord_581663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581680 : List Nat := [2, 1, 1, 1, 2, 5, 3, 2, 4]
def baseStart_581680 : Nat := 118140960795 + 581680 * 2 ^ 59
def prefixEnd_581680 : Nat := 4983230072969 + 3 ^ 40 * 581680 * 2
def baseEnd_581680 : Nat := 132747300936617514677737

theorem tailTrace_581680 : CollatzResearch.WordTrace tailWord_581680 prefixEnd_581680 132747300936617514677737 := by
  unfold tailWord_581680
  simp only [CollatzResearch.WordTrace]
  refine ⟨10607806266340088940003247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14143741688453451920004329 10607806266340088940003247)
  ·
    refine ⟨15911709399510133410004871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10607806266340088940003247 15911709399510133410004871)
    ·
      refine ⟨23867564099265200115007307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15911709399510133410004871 23867564099265200115007307)
      ·
        refine ⟨35801346148897800172510961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23867564099265200115007307 35801346148897800172510961)
        ·
          refine ⟨26851009611673350129383221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35801346148897800172510961 26851009611673350129383221)
          ·
            refine ⟨2517282151094376574629677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26851009611673350129383221 2517282151094376574629677)
            ·
              refine ⟨943980806660391215486129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2517282151094376574629677 943980806660391215486129)
              ·
                refine ⟨707985604995293411614597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 943980806660391215486129 707985604995293411614597)
                ·
                  refine ⟨132747300936617514677737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 707985604995293411614597 132747300936617514677737)
                  ·
                    rfl

theorem cell21_581680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 2, 4].length) (baseStart_581680 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_581680 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_581680 prefixEnd_581680 := by exact prefixLift 581680
  have htrace : WordTrace (prefixWord ++ tailWord_581680) baseStart_581680 baseEnd_581680 := by
    simpa [prefixWord, tailWord_581680, baseEnd_581680] using wordTrace_append hprefix tailTrace_581680
  have hstable : (prefixWord ++ tailWord_581680).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581680).length < 2 ^ (prefixWord ++ tailWord_581680).sum := by decide
  have hdescent : baseEnd_581680 < baseStart_581680 := by decide
  rcases family_descends (prefixWord ++ tailWord_581680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581756 : List Nat := [2, 2, 2, 1, 1, 5, 1, 3, 4]
def baseStart_581756 : Nat := 118140960795 + 581756 * 2 ^ 59
def prefixEnd_581756 : Nat := 4983230072969 + 3 ^ 40 * 581756 * 2
def baseEnd_581756 : Nat := 132764645172058271410915

theorem tailTrace_581756 : CollatzResearch.WordTrace tailWord_581756 prefixEnd_581756 132764645172058271410915 := by
  unfold tailWord_581756
  simp only [CollatzResearch.WordTrace]
  refine ⟨10609192240202421429886561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14145589653603228573182081 10609192240202421429886561)
  ·
    refine ⟨7956894180151816072414921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10609192240202421429886561 7956894180151816072414921)
    ·
      refine ⟨5967670635113862054311191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7956894180151816072414921 5967670635113862054311191)
      ·
        refine ⟨8951505952670793081466787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5967670635113862054311191 8951505952670793081466787)
        ·
          refine ⟨13427258929006189622200181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8951505952670793081466787 13427258929006189622200181)
          ·
            refine ⟨1258805524594330277081267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13427258929006189622200181 1258805524594330277081267)
            ·
              refine ⟨1888208286891495415621901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1258805524594330277081267 1888208286891495415621901)
              ·
                refine ⟨708078107584310780858213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1888208286891495415621901 708078107584310780858213)
                ·
                  refine ⟨132764645172058271410915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 708078107584310780858213 132764645172058271410915)
                  ·
                    rfl

theorem cell21_581756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 3, 4].length) (baseStart_581756 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_581756 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_581756 prefixEnd_581756 := by exact prefixLift 581756
  have htrace : WordTrace (prefixWord ++ tailWord_581756) baseStart_581756 baseEnd_581756 := by
    simpa [prefixWord, tailWord_581756, baseEnd_581756] using wordTrace_append hprefix tailTrace_581756
  have hstable : (prefixWord ++ tailWord_581756).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581756).length < 2 ^ (prefixWord ++ tailWord_581756).sum := by decide
  have hdescent : baseEnd_581756 < baseStart_581756 := by decide
  rcases family_descends (prefixWord ++ tailWord_581756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581770 : List Nat := [3, 1, 2, 3, 1, 2, 2, 7]
def baseStart_581770 : Nat := 118140960795 + 581770 * 2 ^ 59
def prefixEnd_581770 : Nat := 4983230072969 + 3 ^ 40 * 581770 * 2
def baseEnd_581770 : Nat := 44255946720932452725851

theorem tailTrace_581770 : CollatzResearch.WordTrace tailWord_581770 prefixEnd_581770 44255946720932452725851 := by
  unfold tailWord_581770
  simp only [CollatzResearch.WordTrace]
  refine ⟨5304723775588530812695691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14145930068236082167188509 5304723775588530812695691)
  ·
    refine ⟨7957085663382796219043537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5304723775588530812695691 7957085663382796219043537)
    ·
      refine ⟨5967814247537097164282653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7957085663382796219043537 5967814247537097164282653)
      ·
        refine ⟨2237930342826411436605995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5967814247537097164282653 2237930342826411436605995)
        ·
          refine ⟨3356895514239617154908993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2237930342826411436605995 3356895514239617154908993)
          ·
            refine ⟨2517671635679712866181745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3356895514239617154908993 2517671635679712866181745)
            ·
              refine ⟨1888253726759784649636309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2517671635679712866181745 1888253726759784649636309)
              ·
                refine ⟨44255946720932452725851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1888253726759784649636309 44255946720932452725851)
                ·
                  rfl

theorem cell21_581770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 7].length) (baseStart_581770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_581770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_581770 prefixEnd_581770 := by exact prefixLift 581770
  have htrace : WordTrace (prefixWord ++ tailWord_581770) baseStart_581770 baseEnd_581770 := by
    simpa [prefixWord, tailWord_581770, baseEnd_581770] using wordTrace_append hprefix tailTrace_581770
  have hstable : (prefixWord ++ tailWord_581770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581770).length < 2 ^ (prefixWord ++ tailWord_581770).sum := by decide
  have hdescent : baseEnd_581770 < baseStart_581770 := by decide
  rcases family_descends (prefixWord ++ tailWord_581770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581790 : List Nat := [4, 3, 1, 1, 3, 1, 2, 2, 4]
def baseStart_581790 : Nat := 118140960795 + 581790 * 2 ^ 59
def prefixEnd_581790 : Nat := 4983230072969 + 3 ^ 40 * 581790 * 2
def baseEnd_581790 : Nat := 132772404435281767844179

theorem tailTrace_581790 : CollatzResearch.WordTrace tailWord_581790 prefixEnd_581790 132772404435281767844179 := by
  unfold tailWord_581790
  simp only [CollatzResearch.WordTrace]
  refine ⟨2652453070285208333313853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14146416374854444444340549 2652453070285208333313853)
  ·
    refine ⟨994669901356953124992695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2652453070285208333313853 994669901356953124992695)
    ·
      refine ⟨1492004852035429687489043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 994669901356953124992695 1492004852035429687489043)
      ·
        refine ⟨2238007278053144531233565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1492004852035429687489043 2238007278053144531233565)
        ·
          refine ⟨839252729269929199212587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2238007278053144531233565 839252729269929199212587)
          ·
            refine ⟨1258879093904893798818881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 839252729269929199212587 1258879093904893798818881)
            ·
              refine ⟨944159320428670349114161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1258879093904893798818881 944159320428670349114161)
              ·
                refine ⟨708119490321502761835621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 944159320428670349114161 708119490321502761835621)
                ·
                  refine ⟨132772404435281767844179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 708119490321502761835621 132772404435281767844179)
                  ·
                    rfl

theorem cell21_581790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_581790 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_581790 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_581790 prefixEnd_581790 := by exact prefixLift 581790
  have htrace : WordTrace (prefixWord ++ tailWord_581790) baseStart_581790 baseEnd_581790 := by
    simpa [prefixWord, tailWord_581790, baseEnd_581790] using wordTrace_append hprefix tailTrace_581790
  have hstable : (prefixWord ++ tailWord_581790).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581790).length < 2 ^ (prefixWord ++ tailWord_581790).sum := by decide
  have hdescent : baseEnd_581790 < baseStart_581790 := by decide
  rcases family_descends (prefixWord ++ tailWord_581790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581829 : List Nat := [1, 3, 1, 1, 1, 1, 4, 9]
def baseStart_581829 : Nat := 118140960795 + 581829 * 2 ^ 59
def prefixEnd_581829 : Nat := 4983230072969 + 3 ^ 40 * 581829 * 2
def baseEnd_581829 : Nat := 44260434922208788898033

theorem tailTrace_581829 : CollatzResearch.WordTrace tailWord_581829 prefixEnd_581829 44260434922208788898033 := by
  unfold tailWord_581829
  simp only [CollatzResearch.WordTrace]
  refine ⟨21221047009140376327180541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14147364672760250884787027 21221047009140376327180541)
  ·
    refine ⟨7957892628427641122692703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21221047009140376327180541 7957892628427641122692703)
    ·
      refine ⟨11936838942641461684039055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7957892628427641122692703 11936838942641461684039055)
      ·
        refine ⟨17905258413962192526058583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11936838942641461684039055 17905258413962192526058583)
        ·
          refine ⟨26857887620943288789087875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17905258413962192526058583 26857887620943288789087875)
          ·
            refine ⟨40286831431414933183631813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26857887620943288789087875 40286831431414933183631813)
            ·
              refine ⟨7553780893390299971930965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40286831431414933183631813 7553780893390299971930965)
              ·
                refine ⟨44260434922208788898033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7553780893390299971930965 44260434922208788898033)
                ·
                  rfl

theorem cell21_581829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 9].length) (baseStart_581829 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_581829 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_581829 prefixEnd_581829 := by exact prefixLift 581829
  have htrace : WordTrace (prefixWord ++ tailWord_581829) baseStart_581829 baseEnd_581829 := by
    simpa [prefixWord, tailWord_581829, baseEnd_581829] using wordTrace_append hprefix tailTrace_581829
  have hstable : (prefixWord ++ tailWord_581829).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581829).length < 2 ^ (prefixWord ++ tailWord_581829).sum := by decide
  have hdescent : baseEnd_581829 < baseStart_581829 := by decide
  rcases family_descends (prefixWord ++ tailWord_581829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581905 : List Nat := [1, 2, 2, 1, 1, 5, 9]
def baseStart_581905 : Nat := 118140960795 + 581905 * 2 ^ 59
def prefixEnd_581905 : Nat := 4983230072969 + 3 ^ 40 * 581905 * 2
def baseEnd_581905 : Nat := 14755405444674124825253

theorem tailTrace_581905 : CollatzResearch.WordTrace tailWord_581905 prefixEnd_581905 14755405444674124825253 := by
  unfold tailWord_581905
  simp only [CollatzResearch.WordTrace]
  refine ⟨21223818956865041306947169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14149212637910027537964779 21223818956865041306947169)
  ·
    refine ⟨15917864217648780980210377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21223818956865041306947169 15917864217648780980210377)
    ·
      refine ⟨11938398163236585735157783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15917864217648780980210377 11938398163236585735157783)
      ·
        refine ⟨17907597244854878602736675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11938398163236585735157783 17907597244854878602736675)
        ·
          refine ⟨26861395867282317904105013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17907597244854878602736675 26861395867282317904105013)
          ·
            refine ⟨2518255862557717303509845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26861395867282317904105013 2518255862557717303509845)
            ·
              refine ⟨14755405444674124825253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2518255862557717303509845 14755405444674124825253)
              ·
                rfl

theorem cell21_581905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 9].length) (baseStart_581905 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_581905 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_581905 prefixEnd_581905 := by exact prefixLift 581905
  have htrace : WordTrace (prefixWord ++ tailWord_581905) baseStart_581905 baseEnd_581905 := by
    simpa [prefixWord, tailWord_581905, baseEnd_581905] using wordTrace_append hprefix tailTrace_581905
  have hstable : (prefixWord ++ tailWord_581905).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581905).length < 2 ^ (prefixWord ++ tailWord_581905).sum := by decide
  have hdescent : baseEnd_581905 < baseStart_581905 := by decide
  rcases family_descends (prefixWord ++ tailWord_581905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581911 : List Nat := [1, 1, 3, 4, 1, 3, 3, 2, 3]
def baseStart_581911 : Nat := 118140960795 + 581911 * 2 ^ 59
def prefixEnd_581911 : Nat := 4983230072969 + 3 ^ 40 * 581911 * 2
def baseEnd_581911 : Nat := 132800018283812446327265

theorem tailTrace_581911 : CollatzResearch.WordTrace tailWord_581911 prefixEnd_581911 132800018283812446327265 := by
  unfold tailWord_581911
  simp only [CollatzResearch.WordTrace]
  refine ⟨21224037794843304331665587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14149358529895536221110391 21224037794843304331665587)
  ·
    refine ⟨31836056692264956497498381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21224037794843304331665587 31836056692264956497498381)
    ·
      refine ⟨11938521259599358686561893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31836056692264956497498381 11938521259599358686561893)
      ·
        refine ⟨2238472736174879753730355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11938521259599358686561893 2238472736174879753730355)
        ·
          refine ⟨3357709104262319630595533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2238472736174879753730355 3357709104262319630595533)
          ·
            refine ⟨1259140914098369861473325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3357709104262319630595533 1259140914098369861473325)
            ·
              refine ⟨472177842786888698052497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1259140914098369861473325 472177842786888698052497)
              ·
                refine ⟨354133382090166523539373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 472177842786888698052497 354133382090166523539373)
                ·
                  refine ⟨132800018283812446327265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 354133382090166523539373 132800018283812446327265)
                  ·
                    rfl

theorem cell21_581911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 2, 3].length) (baseStart_581911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_581911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_581911 prefixEnd_581911 := by exact prefixLift 581911
  have htrace : WordTrace (prefixWord ++ tailWord_581911) baseStart_581911 baseEnd_581911 := by
    simpa [prefixWord, tailWord_581911, baseEnd_581911] using wordTrace_append hprefix tailTrace_581911
  have hstable : (prefixWord ++ tailWord_581911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581911).length < 2 ^ (prefixWord ++ tailWord_581911).sum := by decide
  have hdescent : baseEnd_581911 < baseStart_581911 := by decide
  rcases family_descends (prefixWord ++ tailWord_581911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581922 : List Nat := [3, 3, 1, 1, 3, 1, 1, 8]
def baseStart_581922 : Nat := 118140960795 + 581922 * 2 ^ 59
def prefixEnd_581922 : Nat := 4983230072969 + 3 ^ 40 * 581922 * 2
def baseEnd_581922 : Nat := 44267509544559623881303

theorem tailTrace_581922 : CollatzResearch.WordTrace tailWord_581922 prefixEnd_581922 44267509544559623881303 := by
  unfold tailWord_581922
  simp only [CollatzResearch.WordTrace]
  refine ⟨5306109749450863302579005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14149625998535635473544013 5306109749450863302579005)
  ·
    refine ⟨1989791156044073738467127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5306109749450863302579005 1989791156044073738467127)
    ·
      refine ⟨2984686734066110607700691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1989791156044073738467127 2984686734066110607700691)
      ·
        refine ⟨4477030101099165911551037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2984686734066110607700691 4477030101099165911551037)
        ·
          refine ⟨1678886287912187216831639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4477030101099165911551037 1678886287912187216831639)
          ·
            refine ⟨2518329431868280825247459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1678886287912187216831639 2518329431868280825247459)
            ·
              refine ⟨3777494147802421237871189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2518329431868280825247459 3777494147802421237871189)
              ·
                refine ⟨44267509544559623881303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3777494147802421237871189 44267509544559623881303)
                ·
                  rfl

theorem cell21_581922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 8].length) (baseStart_581922 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_581922 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_581922 prefixEnd_581922 := by exact prefixLift 581922
  have htrace : WordTrace (prefixWord ++ tailWord_581922) baseStart_581922 baseEnd_581922 := by
    simpa [prefixWord, tailWord_581922, baseEnd_581922] using wordTrace_append hprefix tailTrace_581922
  have hstable : (prefixWord ++ tailWord_581922).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581922).length < 2 ^ (prefixWord ++ tailWord_581922).sum := by decide
  have hdescent : baseEnd_581922 < baseStart_581922 := by decide
  rcases family_descends (prefixWord ++ tailWord_581922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582046 : List Nat := [4, 3, 1, 2, 1, 1, 2, 2, 5]
def baseStart_582046 : Nat := 118140960795 + 582046 * 2 ^ 59
def prefixEnd_582046 : Nat := 4983230072969 + 3 ^ 40 * 582046 * 2
def baseEnd_582046 : Nat := 132830827123082211576989

theorem tailTrace_582046 : CollatzResearch.WordTrace tailWord_582046 prefixEnd_582046 132830827123082211576989 := by
  unfold tailWord_582046
  simp only [CollatzResearch.WordTrace]
  refine ⟨2653620206169277798478749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14152641099569481591886661 2653620206169277798478749)
  ·
    refine ⟨995107577313479174429531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2653620206169277798478749 995107577313479174429531)
    ·
      refine ⟨1492661365970218761644297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 995107577313479174429531 1492661365970218761644297)
      ·
        refine ⟨1119496024477664071233223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1492661365970218761644297 1119496024477664071233223)
        ·
          refine ⟨1679244036716496106849835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1119496024477664071233223 1679244036716496106849835)
          ·
            refine ⟨2518866055074744160274753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1679244036716496106849835 2518866055074744160274753)
            ·
              refine ⟨1889149541306058120206065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2518866055074744160274753 1889149541306058120206065)
              ·
                refine ⟨1416862155979543590154549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1889149541306058120206065 1416862155979543590154549)
                ·
                  refine ⟨132830827123082211576989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1416862155979543590154549 132830827123082211576989)
                  ·
                    rfl

theorem cell21_582046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_582046 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_582046 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_582046 prefixEnd_582046 := by exact prefixLift 582046
  have htrace : WordTrace (prefixWord ++ tailWord_582046) baseStart_582046 baseEnd_582046 := by
    simpa [prefixWord, tailWord_582046, baseEnd_582046] using wordTrace_append hprefix tailTrace_582046
  have hstable : (prefixWord ++ tailWord_582046).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582046).length < 2 ^ (prefixWord ++ tailWord_582046).sum := by decide
  have hdescent : baseEnd_582046 < baseStart_582046 := by decide
  rcases family_descends (prefixWord ++ tailWord_582046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582049 : List Nat := [1, 2, 3, 5, 2, 1, 2, 5]
def baseStart_582049 : Nat := 118140960795 + 582049 * 2 ^ 59
def prefixEnd_582049 : Nat := 4983230072969 + 3 ^ 40 * 582049 * 2
def baseEnd_582049 : Nat := 44277170587984957675661

theorem tailTrace_582049 : CollatzResearch.WordTrace tailWord_582049 prefixEnd_582049 44277170587984957675661 := by
  unfold tailWord_582049
  simp only [CollatzResearch.WordTrace]
  refine ⟨21229071068343353900189201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14152714045562235933459467 21229071068343353900189201)
  ·
    refine ⟨15921803301257515425141901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21229071068343353900189201 15921803301257515425141901)
    ·
      refine ⟨5970676237971568284428213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15921803301257515425141901 5970676237971568284428213)
      ·
        refine ⟨559750897309834526665145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5970676237971568284428213 559750897309834526665145)
        ·
          refine ⟨419813172982375894998859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 559750897309834526665145 419813172982375894998859)
          ·
            refine ⟨629719759473563842498289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 419813172982375894998859 629719759473563842498289)
            ·
              refine ⟨472289819605172881873717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 629719759473563842498289 472289819605172881873717)
              ·
                refine ⟨44277170587984957675661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 472289819605172881873717 44277170587984957675661)
                ·
                  rfl

theorem cell21_582049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 5].length) (baseStart_582049 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_582049 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_582049 prefixEnd_582049 := by exact prefixLift 582049
  have htrace : WordTrace (prefixWord ++ tailWord_582049) baseStart_582049 baseEnd_582049 := by
    simpa [prefixWord, tailWord_582049, baseEnd_582049] using wordTrace_append hprefix tailTrace_582049
  have hstable : (prefixWord ++ tailWord_582049).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582049).length < 2 ^ (prefixWord ++ tailWord_582049).sum := by decide
  have hdescent : baseEnd_582049 < baseStart_582049 := by decide
  rcases family_descends (prefixWord ++ tailWord_582049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582181 : List Nat := [1, 3, 1, 2, 2, 1, 3, 5, 3]
def baseStart_582181 : Nat := 118140960795 + 582181 * 2 ^ 59
def prefixEnd_582181 : Nat := 4983230072969 + 3 ^ 40 * 582181 * 2
def baseEnd_582181 : Nat := 132861635962351976826713

theorem tailTrace_582181 : CollatzResearch.WordTrace tailWord_582181 prefixEnd_582181 132861635962351976826713 := by
  unfold tailWord_582181
  simp only [CollatzResearch.WordTrace]
  refine ⟨21233885503865140443994397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14155923669243426962662931 21233885503865140443994397)
  ·
    refine ⟨7962707063949427666497899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21233885503865140443994397 7962707063949427666497899)
    ·
      refine ⟨11944060595924141499746849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7962707063949427666497899 11944060595924141499746849)
      ·
        refine ⟨8958045446943106124810137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11944060595924141499746849 8958045446943106124810137)
        ·
          refine ⟨6718534085207329593607603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8958045446943106124810137 6718534085207329593607603)
          ·
            refine ⟨10077801127810994390411405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6718534085207329593607603 10077801127810994390411405)
            ·
              refine ⟨3779175422929122896404277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10077801127810994390411405 3779175422929122896404277)
              ·
                refine ⟨354297695899605271537901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3779175422929122896404277 354297695899605271537901)
                ·
                  refine ⟨132861635962351976826713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 354297695899605271537901 132861635962351976826713)
                  ·
                    rfl

theorem cell21_582181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 5, 3].length) (baseStart_582181 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_582181 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_582181 prefixEnd_582181 := by exact prefixLift 582181
  have htrace : WordTrace (prefixWord ++ tailWord_582181) baseStart_582181 baseEnd_582181 := by
    simpa [prefixWord, tailWord_582181, baseEnd_582181] using wordTrace_append hprefix tailTrace_582181
  have hstable : (prefixWord ++ tailWord_582181).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582181).length < 2 ^ (prefixWord ++ tailWord_582181).sum := by decide
  have hdescent : baseEnd_582181 < baseStart_582181 := by decide
  rcases family_descends (prefixWord ++ tailWord_582181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582198 : List Nat := [5, 1, 2, 1, 2, 2, 2, 1, 5]
def baseStart_582198 : Nat := 118140960795 + 582198 * 2 ^ 59
def prefixEnd_582198 : Nat := 4983230072969 + 3 ^ 40 * 582198 * 2
def baseEnd_582198 : Nat := 132865515593963725043345

theorem tailTrace_582198 : CollatzResearch.WordTrace tailWord_582198 prefixEnd_582198 132865515593963725043345 := by
  unfold tailWord_582198
  simp only [CollatzResearch.WordTrace]
  refine ⟨1327156596550222021710203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14156337029869034898242165 1327156596550222021710203)
  ·
    refine ⟨1990734894825333032565305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1327156596550222021710203 1990734894825333032565305)
    ·
      refine ⟨1493051171118999774423979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1990734894825333032565305 1493051171118999774423979)
      ·
        refine ⟨2239576756678499661635969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1493051171118999774423979 2239576756678499661635969)
        ·
          refine ⟨1679682567508874746226977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2239576756678499661635969 1679682567508874746226977)
          ·
            refine ⟨1259761925631656059670233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1679682567508874746226977 1259761925631656059670233)
            ·
              refine ⟨944821444223742044752675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1259761925631656059670233 944821444223742044752675)
              ·
                refine ⟨1417232166335613067129013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 944821444223742044752675 1417232166335613067129013)
                ·
                  refine ⟨132865515593963725043345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1417232166335613067129013 132865515593963725043345)
                  ·
                    rfl

theorem cell21_582198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_582198 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_582198 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_582198 prefixEnd_582198 := by exact prefixLift 582198
  have htrace : WordTrace (prefixWord ++ tailWord_582198) baseStart_582198 baseEnd_582198 := by
    simpa [prefixWord, tailWord_582198, baseEnd_582198] using wordTrace_append hprefix tailTrace_582198
  have hstable : (prefixWord ++ tailWord_582198).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582198).length < 2 ^ (prefixWord ++ tailWord_582198).sum := by decide
  have hdescent : baseEnd_582198 < baseStart_582198 := by decide
  rcases family_descends (prefixWord ++ tailWord_582198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582350 : List Nat := [4, 1, 1, 1, 3, 3, 2, 3, 3]
def baseStart_582350 : Nat := 118140960795 + 582350 * 2 ^ 59
def prefixEnd_582350 : Nat := 4983230072969 + 3 ^ 40 * 582350 * 2
def baseEnd_582350 : Nat := 132900204064845238509701

theorem tailTrace_582350 : CollatzResearch.WordTrace tailWord_582350 prefixEnd_582350 132900204064845238509701 := by
  unfold tailWord_582350
  simp only [CollatzResearch.WordTrace]
  refine ⟨2655006180031610288362063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14160032960168588204597669 2655006180031610288362063)
  ·
    refine ⟨3982509270047415432543095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2655006180031610288362063 3982509270047415432543095)
    ·
      refine ⟨5973763905071123148814643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3982509270047415432543095 5973763905071123148814643)
      ·
        refine ⟨8960645857606684723221965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5973763905071123148814643 8960645857606684723221965)
        ·
          refine ⟨3360242196602506771208237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8960645857606684723221965 3360242196602506771208237)
          ·
            refine ⟨1260090823725940039203089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3360242196602506771208237 1260090823725940039203089)
            ·
              refine ⟨945068117794455029402317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1260090823725940039203089 945068117794455029402317)
              ·
                refine ⟨354400544172920636025869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 945068117794455029402317 354400544172920636025869)
                ·
                  refine ⟨132900204064845238509701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 354400544172920636025869 132900204064845238509701)
                  ·
                    rfl

theorem cell21_582350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 3, 3].length) (baseStart_582350 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_582350 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_582350 prefixEnd_582350 := by exact prefixLift 582350
  have htrace : WordTrace (prefixWord ++ tailWord_582350) baseStart_582350 baseEnd_582350 := by
    simpa [prefixWord, tailWord_582350, baseEnd_582350] using wordTrace_append hprefix tailTrace_582350
  have hstable : (prefixWord ++ tailWord_582350).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582350).length < 2 ^ (prefixWord ++ tailWord_582350).sum := by decide
  have hdescent : baseEnd_582350 < baseStart_582350 := by decide
  rcases family_descends (prefixWord ++ tailWord_582350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582364 : List Nat := [2, 2, 5, 1, 1, 2, 1, 1, 6]
def baseStart_582364 : Nat := 118140960795 + 582364 * 2 ^ 59
def prefixEnd_582364 : Nat := 4983230072969 + 3 ^ 40 * 582364 * 2
def baseEnd_582364 : Nat := 132903399055584325276339

theorem tailTrace_582364 : CollatzResearch.WordTrace tailWord_582364 prefixEnd_582364 132903399055584325276339 := by
  unfold tailWord_582364
  simp only [CollatzResearch.WordTrace]
  refine ⟨10620280031101081348953073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14160373374801441798604097 10620280031101081348953073)
  ·
    refine ⟨7965210023325811011714805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10620280031101081348953073 7965210023325811011714805)
    ·
      refine ⟨746738439686794782348263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7965210023325811011714805 746738439686794782348263)
      ·
        refine ⟨1120107659530192173522395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 746738439686794782348263 1120107659530192173522395)
        ·
          refine ⟨1680161489295288260283593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1120107659530192173522395 1680161489295288260283593)
          ·
            refine ⟨1260121116971466195212695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1680161489295288260283593 1260121116971466195212695)
            ·
              refine ⟨1890181675457199292819043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1260121116971466195212695 1890181675457199292819043)
              ·
                refine ⟨2835272513185798939228565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1890181675457199292819043 2835272513185798939228565)
                ·
                  refine ⟨132903399055584325276339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2835272513185798939228565 132903399055584325276339)
                  ·
                    rfl

theorem cell21_582364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 6].length) (baseStart_582364 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_582364 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_582364 prefixEnd_582364 := by exact prefixLift 582364
  have htrace : WordTrace (prefixWord ++ tailWord_582364) baseStart_582364 baseEnd_582364 := by
    simpa [prefixWord, tailWord_582364, baseEnd_582364] using wordTrace_append hprefix tailTrace_582364
  have hstable : (prefixWord ++ tailWord_582364).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582364).length < 2 ^ (prefixWord ++ tailWord_582364).sum := by decide
  have hdescent : baseEnd_582364 < baseStart_582364 := by decide
  rcases family_descends (prefixWord ++ tailWord_582364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582409 : List Nat := [1, 2, 1, 1, 3, 2, 5, 3, 3]
def baseStart_582409 : Nat := 118140960795 + 582409 * 2 ^ 59
def prefixEnd_582409 : Nat := 4983230072969 + 3 ^ 40 * 582409 * 2
def baseEnd_582409 : Nat := 132913668668674247026247

theorem tailTrace_582409 : CollatzResearch.WordTrace tailWord_582409 prefixEnd_582409 132913668668674247026247 := by
  unfold tailWord_582409
  simp only [CollatzResearch.WordTrace]
  refine ⟨21242201347039135383294281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14161467564692756922196187 21242201347039135383294281)
  ·
    refine ⟨15931651010279351537470711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21242201347039135383294281 15931651010279351537470711)
    ·
      refine ⟨23897476515419027306206067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15931651010279351537470711 23897476515419027306206067)
      ·
        refine ⟨35846214773128540959309101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23897476515419027306206067 35846214773128540959309101)
        ·
          refine ⟨13442330539923202859740913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35846214773128540959309101 13442330539923202859740913)
          ·
            refine ⟨10081747904942402144805685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13442330539923202859740913 10081747904942402144805685)
            ·
              refine ⟨945163866088350201075533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10081747904942402144805685 945163866088350201075533)
              ·
                refine ⟨354436449783131325403325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 945163866088350201075533 354436449783131325403325)
                ·
                  refine ⟨132913668668674247026247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 354436449783131325403325 132913668668674247026247)
                  ·
                    rfl

theorem cell21_582409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 3, 3].length) (baseStart_582409 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_582409 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_582409 prefixEnd_582409 := by exact prefixLift 582409
  have htrace : WordTrace (prefixWord ++ tailWord_582409) baseStart_582409 baseEnd_582409 := by
    simpa [prefixWord, tailWord_582409, baseEnd_582409] using wordTrace_append hprefix tailTrace_582409
  have hstable : (prefixWord ++ tailWord_582409).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582409).length < 2 ^ (prefixWord ++ tailWord_582409).sum := by decide
  have hdescent : baseEnd_582409 < baseStart_582409 := by decide
  rcases family_descends (prefixWord ++ tailWord_582409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582426 : List Nat := [3, 1, 1, 3, 2, 1, 5, 2, 3]
def baseStart_582426 : Nat := 118140960795 + 582426 * 2 ^ 59
def prefixEnd_582426 : Nat := 4983230072969 + 3 ^ 40 * 582426 * 2
def baseEnd_582426 : Nat := 132917548300285995242879

theorem tailTrace_582426 : CollatzResearch.WordTrace tailWord_582426 prefixEnd_582426 132917548300285995242879 := by
  unfold tailWord_582426
  simp only [CollatzResearch.WordTrace]
  refine ⟨5310705346994386821665783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14161880925318364857775421 5310705346994386821665783)
  ·
    refine ⟨7966058020491580232498675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5310705346994386821665783 7966058020491580232498675)
    ·
      refine ⟨11949087030737370348748013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7966058020491580232498675 11949087030737370348748013)
      ·
        refine ⟨4480907636526513880780505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11949087030737370348748013 4480907636526513880780505)
        ·
          refine ⟨3360680727394885410585379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4480907636526513880780505 3360680727394885410585379)
          ·
            refine ⟨5041021091092328115878069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3360680727394885410585379 5041021091092328115878069)
            ·
              refine ⟨472595727289905760863569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5041021091092328115878069 472595727289905760863569)
              ·
                refine ⟨354446795467429320647677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 472595727289905760863569 354446795467429320647677)
                ·
                  refine ⟨132917548300285995242879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 354446795467429320647677 132917548300285995242879)
                  ·
                    rfl

theorem cell21_582426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 2, 3].length) (baseStart_582426 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_582426 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_582426 prefixEnd_582426 := by exact prefixLift 582426
  have htrace : WordTrace (prefixWord ++ tailWord_582426) baseStart_582426 baseEnd_582426 := by
    simpa [prefixWord, tailWord_582426, baseEnd_582426] using wordTrace_append hprefix tailTrace_582426
  have hstable : (prefixWord ++ tailWord_582426).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582426).length < 2 ^ (prefixWord ++ tailWord_582426).sum := by decide
  have hdescent : baseEnd_582426 < baseStart_582426 := by decide
  rcases family_descends (prefixWord ++ tailWord_582426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582437 : List Nat := [1, 3, 1, 2, 3, 1, 4, 6]
def baseStart_582437 : Nat := 118140960795 + 582437 * 2 ^ 59
def prefixEnd_582437 : Nat := 4983230072969 + 3 ^ 40 * 582437 * 2
def baseEnd_582437 : Nat := 44306686216717473519841

theorem tailTrace_582437 : CollatzResearch.WordTrace tailWord_582437 prefixEnd_582437 44306686216717473519841 := by
  unfold tailWord_582437
  simp only [CollatzResearch.WordTrace]
  refine ⟨21243222590937696165313565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14162148393958464110209043 21243222590937696165313565)
  ·
    refine ⟨7966208471601636061992587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21243222590937696165313565 7966208471601636061992587)
    ·
      refine ⟨11949312707402454092988881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7966208471601636061992587 11949312707402454092988881)
      ·
        refine ⟨8961984530551840569741661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11949312707402454092988881 8961984530551840569741661)
        ·
          refine ⟨3360744198956940213653123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8961984530551840569741661 3360744198956940213653123)
          ·
            refine ⟨5041116298435410320479685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3360744198956940213653123 5041116298435410320479685)
            ·
              refine ⟨945209305956639435089941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5041116298435410320479685 945209305956639435089941)
              ·
                refine ⟨44306686216717473519841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 945209305956639435089941 44306686216717473519841)
                ·
                  rfl

theorem cell21_582437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 6].length) (baseStart_582437 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_582437 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_582437 prefixEnd_582437 := by exact prefixLift 582437
  have htrace : WordTrace (prefixWord ++ tailWord_582437) baseStart_582437 baseEnd_582437 := by
    simpa [prefixWord, tailWord_582437, baseEnd_582437] using wordTrace_append hprefix tailTrace_582437
  have hstable : (prefixWord ++ tailWord_582437).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582437).length < 2 ^ (prefixWord ++ tailWord_582437).sum := by decide
  have hdescent : baseEnd_582437 < baseStart_582437 := by decide
  rcases family_descends (prefixWord ++ tailWord_582437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582477 : List Nat := [1, 6, 1, 2, 3, 1, 2, 2, 3]
def baseStart_582477 : Nat := 118140960795 + 582477 * 2 ^ 59
def prefixEnd_582477 : Nat := 4983230072969 + 3 ^ 40 * 582477 * 2
def baseEnd_582477 : Nat := 132929187195121239892775

theorem tailTrace_582477 : CollatzResearch.WordTrace tailWord_582477 prefixEnd_582477 132929187195121239892775 := by
  unfold tailWord_582477
  simp only [CollatzResearch.WordTrace]
  refine ⟨21244681510792782996769685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14163121007195188664513123 21244681510792782996769685)
  ·
    refine ⟨995844445818411702973579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 21244681510792782996769685 995844445818411702973579)
    ·
      refine ⟨1493766668727617554460369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 995844445818411702973579 1493766668727617554460369)
      ·
        refine ⟨1120325001545713165845277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1493766668727617554460369 1120325001545713165845277)
        ·
          refine ⟨420121875579642437191979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1120325001545713165845277 420121875579642437191979)
          ·
            refine ⟨630182813369463655787969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 420121875579642437191979 630182813369463655787969)
            ·
              refine ⟨472637110027097741840977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 630182813369463655787969 472637110027097741840977)
              ·
                refine ⟨354477832520323306380733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 472637110027097741840977 354477832520323306380733)
                ·
                  refine ⟨132929187195121239892775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 354477832520323306380733 132929187195121239892775)
                  ·
                    rfl

theorem cell21_582477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_582477 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_582477 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_582477 prefixEnd_582477 := by exact prefixLift 582477
  have htrace : WordTrace (prefixWord ++ tailWord_582477) baseStart_582477 baseEnd_582477 := by
    simpa [prefixWord, tailWord_582477, baseEnd_582477] using wordTrace_append hprefix tailTrace_582477
  have hstable : (prefixWord ++ tailWord_582477).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582477).length < 2 ^ (prefixWord ++ tailWord_582477).sum := by decide
  have hdescent : baseEnd_582477 < baseStart_582477 := by decide
  rcases family_descends (prefixWord ++ tailWord_582477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582485 : List Nat := [1, 3, 2, 2, 2, 1, 3, 4, 3]
def baseStart_582485 : Nat := 118140960795 + 582485 * 2 ^ 59
def prefixEnd_582485 : Nat := 4983230072969 + 3 ^ 40 * 582485 * 2
def baseEnd_582485 : Nat := 132931012904115003759425

theorem tailTrace_582485 : CollatzResearch.WordTrace tailWord_582485 prefixEnd_582485 132931012904115003759425 := by
  unfold tailWord_582485
  simp only [CollatzResearch.WordTrace]
  refine ⟨21244973294763800363060909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14163315529842533575373939 21244973294763800363060909)
  ·
    refine ⟨7966864985536425136147841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21244973294763800363060909 7966864985536425136147841)
    ·
      refine ⟨5975148739152318852110881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7966864985536425136147841 5975148739152318852110881)
      ·
        refine ⟨4481361554364239139083161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5975148739152318852110881 4481361554364239139083161)
        ·
          refine ⟨3361021165773179354312371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4481361554364239139083161 3361021165773179354312371)
          ·
            refine ⟨5041531748659769031468557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3361021165773179354312371 5041531748659769031468557)
            ·
              refine ⟨1890574405747413386800709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5041531748659769031468557 1890574405747413386800709)
              ·
                refine ⟨354482701077640010025133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1890574405747413386800709 354482701077640010025133)
                ·
                  refine ⟨132931012904115003759425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 354482701077640010025133 132931012904115003759425)
                  ·
                    rfl

theorem cell21_582485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 4, 3].length) (baseStart_582485 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_582485 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_582485 prefixEnd_582485 := by exact prefixLift 582485
  have htrace : WordTrace (prefixWord ++ tailWord_582485) baseStart_582485 baseEnd_582485 := by
    simpa [prefixWord, tailWord_582485, baseEnd_582485] using wordTrace_append hprefix tailTrace_582485
  have hstable : (prefixWord ++ tailWord_582485).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582485).length < 2 ^ (prefixWord ++ tailWord_582485).sum := by decide
  have hdescent : baseEnd_582485 < baseStart_582485 := by decide
  rcases family_descends (prefixWord ++ tailWord_582485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582499 : List Nat := [1, 1, 1, 5, 3, 1, 2, 3, 4]
def baseStart_582499 : Nat := 118140960795 + 582499 * 2 ^ 59
def prefixEnd_582499 : Nat := 4983230072969 + 3 ^ 40 * 582499 * 2
def baseEnd_582499 : Nat := 132934207894854090526063

theorem tailTrace_582499 : CollatzResearch.WordTrace tailWord_582499 prefixEnd_582499 132934207894854090526063 := by
  unfold tailWord_582499
  simp only [CollatzResearch.WordTrace]
  refine ⟨21245483916713080754070551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14163655944475387169380367 21245483916713080754070551)
  ·
    refine ⟨31868225875069621131105827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21245483916713080754070551 31868225875069621131105827)
    ·
      refine ⟨47802338812604431696658741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31868225875069621131105827 47802338812604431696658741)
      ·
        refine ⟨4481469263681665471561757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47802338812604431696658741 4481469263681665471561757)
        ·
          refine ⟨1680550973880624551835659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4481469263681665471561757 1680550973880624551835659)
          ·
            refine ⟨2520826460820936827753489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1680550973880624551835659 2520826460820936827753489)
            ·
              refine ⟨1890619845615702620815117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2520826460820936827753489 1890619845615702620815117)
              ·
                refine ⟨708982442105888482805669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1890619845615702620815117 708982442105888482805669)
                ·
                  refine ⟨132934207894854090526063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 708982442105888482805669 132934207894854090526063)
                  ·
                    rfl

theorem cell21_582499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 3, 4].length) (baseStart_582499 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_582499 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_582499 prefixEnd_582499 := by exact prefixLift 582499
  have htrace : WordTrace (prefixWord ++ tailWord_582499) baseStart_582499 baseEnd_582499 := by
    simpa [prefixWord, tailWord_582499, baseEnd_582499] using wordTrace_append hprefix tailTrace_582499
  have hstable : (prefixWord ++ tailWord_582499).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582499).length < 2 ^ (prefixWord ++ tailWord_582499).sum := by decide
  have hdescent : baseEnd_582499 < baseStart_582499 := by decide
  rcases family_descends (prefixWord ++ tailWord_582499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582572 : List Nat := [2, 2, 1, 1, 1, 1, 2, 11]
def baseStart_582572 : Nat := 118140960795 + 582572 * 2 ^ 59
def prefixEnd_582572 : Nat := 4983230072969 + 3 ^ 40 * 582572 * 2
def baseEnd_582572 : Nat := 44316955829807395269749

theorem tailTrace_582572 : CollatzResearch.WordTrace tailWord_582572 prefixEnd_582572 44316955829807395269749 := by
  unfold tailWord_582572
  simp only [CollatzResearch.WordTrace]
  refine ⟨10624073222724307110738985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14165430963632409480985313 10624073222724307110738985)
  ·
    refine ⟨7968054917043230333054239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10624073222724307110738985 7968054917043230333054239)
    ·
      refine ⟨11952082375564845499581359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7968054917043230333054239 11952082375564845499581359)
      ·
        refine ⟨17928123563347268249372039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11952082375564845499581359 17928123563347268249372039)
        ·
          refine ⟨26892185345020902374058059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17928123563347268249372039 26892185345020902374058059)
          ·
            refine ⟨40338278017531353561087089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26892185345020902374058059 40338278017531353561087089)
            ·
              refine ⟨30253708513148515170815317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40338278017531353561087089 30253708513148515170815317)
              ·
                refine ⟨44316955829807395269749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 30253708513148515170815317 44316955829807395269749)
                ·
                  rfl

theorem cell21_582572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 11].length) (baseStart_582572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_582572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_582572 prefixEnd_582572 := by exact prefixLift 582572
  have htrace : WordTrace (prefixWord ++ tailWord_582572) baseStart_582572 baseEnd_582572 := by
    simpa [prefixWord, tailWord_582572, baseEnd_582572] using wordTrace_append hprefix tailTrace_582572
  have hstable : (prefixWord ++ tailWord_582572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582572).length < 2 ^ (prefixWord ++ tailWord_582572).sum := by decide
  have hdescent : baseEnd_582572 < baseStart_582572 := by decide
  rcases family_descends (prefixWord ++ tailWord_582572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582713 : List Nat := [1, 2, 1, 5, 2, 1, 2, 4, 3]
def baseStart_582713 : Nat := 118140960795 + 582713 * 2 ^ 59
def prefixEnd_582713 : Nat := 4983230072969 + 3 ^ 40 * 582713 * 2
def baseEnd_582713 : Nat := 132983045610437273958959

theorem tailTrace_582713 : CollatzResearch.WordTrace tailWord_582713 prefixEnd_582713 132983045610437273958959 := by
  unfold tailWord_582713
  simp only [CollatzResearch.WordTrace]
  refine ⟨21253289137937795302360793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14168859425291863534907195 21253289137937795302360793)
  ·
    refine ⟨15939966853453346476770595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21253289137937795302360793 15939966853453346476770595)
    ·
      refine ⟨23909950280180019715155893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15939966853453346476770595 23909950280180019715155893)
      ·
        refine ⟨2241557838766876848295865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23909950280180019715155893 2241557838766876848295865)
        ·
          refine ⟨1681168379075157636221899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2241557838766876848295865 1681168379075157636221899)
          ·
            refine ⟨2521752568612736454332849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1681168379075157636221899 2521752568612736454332849)
            ·
              refine ⟨1891314426459552340749637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2521752568612736454332849 1891314426459552340749637)
              ·
                refine ⟨354621454961166063890557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1891314426459552340749637 354621454961166063890557)
                ·
                  refine ⟨132983045610437273958959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 354621454961166063890557 132983045610437273958959)
                  ·
                    rfl

theorem cell21_582713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 4, 3].length) (baseStart_582713 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_582713 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_582713 prefixEnd_582713 := by exact prefixLift 582713
  have htrace : WordTrace (prefixWord ++ tailWord_582713) baseStart_582713 baseEnd_582713 := by
    simpa [prefixWord, tailWord_582713, baseEnd_582713] using wordTrace_append hprefix tailTrace_582713
  have hstable : (prefixWord ++ tailWord_582713).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582713).length < 2 ^ (prefixWord ++ tailWord_582713).sum := by decide
  have hdescent : baseEnd_582713 < baseStart_582713 := by decide
  rcases family_descends (prefixWord ++ tailWord_582713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582823 : List Nat := [1, 1, 6, 2, 1, 3, 2, 2, 3]
def baseStart_582823 : Nat := 118140960795 + 582823 * 2 ^ 59
def prefixEnd_582823 : Nat := 4983230072969 + 3 ^ 40 * 582823 * 2
def baseEnd_582823 : Nat := 133008149109101527125401

theorem tailTrace_582823 : CollatzResearch.WordTrace tailWord_582823 prefixEnd_582823 133008149109101527125401 := by
  unfold tailWord_582823
  simp only [CollatzResearch.WordTrace]
  refine ⟨21257301167539284088865123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14171534111692856059243415 21257301167539284088865123)
  ·
    refine ⟨31885951751308926133297685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21257301167539284088865123 31885951751308926133297685)
    ·
      refine ⟨1494653988342605912498329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 31885951751308926133297685 1494653988342605912498329)
      ·
        refine ⟨1120990491256954434373747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1494653988342605912498329 1120990491256954434373747)
        ·
          refine ⟨1681485736885431651560621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1120990491256954434373747 1681485736885431651560621)
          ·
            refine ⟨630557151332036869335233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1681485736885431651560621 630557151332036869335233)
            ·
              refine ⟨472917863499027652001425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 630557151332036869335233 472917863499027652001425)
              ·
                refine ⟨354688397624270739001069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 472917863499027652001425 354688397624270739001069)
                ·
                  refine ⟨133008149109101527125401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 354688397624270739001069 133008149109101527125401)
                  ·
                    rfl

theorem cell21_582823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 2, 3].length) (baseStart_582823 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_582823 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_582823 prefixEnd_582823 := by exact prefixLift 582823
  have htrace : WordTrace (prefixWord ++ tailWord_582823) baseStart_582823 baseEnd_582823 := by
    simpa [prefixWord, tailWord_582823, baseEnd_582823] using wordTrace_append hprefix tailTrace_582823
  have hstable : (prefixWord ++ tailWord_582823).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582823).length < 2 ^ (prefixWord ++ tailWord_582823).sum := by decide
  have hdescent : baseEnd_582823 < baseStart_582823 := by decide
  rcases family_descends (prefixWord ++ tailWord_582823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582848 : List Nat := [2, 1, 1, 2, 6, 1, 1, 2, 5]
def baseStart_582848 : Nat := 118140960795 + 582848 * 2 ^ 59
def prefixEnd_582848 : Nat := 4983230072969 + 3 ^ 40 * 582848 * 2
def baseEnd_582848 : Nat := 133013854449707039208683

theorem tailTrace_582848 : CollatzResearch.WordTrace tailWord_582848 prefixEnd_582848 133013854449707039208683 := by
  unfold tailWord_582848
  simp only [CollatzResearch.WordTrace]
  refine ⟨10629106496224356679262599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14172141994965808905683465 10629106496224356679262599)
  ·
    refine ⟨15943659744336535018893899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10629106496224356679262599 15943659744336535018893899)
    ·
      refine ⟨23915489616504802528340849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15943659744336535018893899 23915489616504802528340849)
      ·
        refine ⟨17936617212378601896255637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23915489616504802528340849 17936617212378601896255637)
        ·
          refine ⟨840778931830246963886983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 17936617212378601896255637 840778931830246963886983)
          ·
            refine ⟨1261168397745370445830475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 840778931830246963886983 1261168397745370445830475)
            ·
              refine ⟨1891752596618055668745713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1261168397745370445830475 1891752596618055668745713)
              ·
                refine ⟨1418814447463541751559285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1891752596618055668745713 1418814447463541751559285)
                ·
                  refine ⟨133013854449707039208683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1418814447463541751559285 133013854449707039208683)
                  ·
                    rfl

theorem cell21_582848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 2, 5].length) (baseStart_582848 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_582848 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_582848 prefixEnd_582848 := by exact prefixLift 582848
  have htrace : WordTrace (prefixWord ++ tailWord_582848) baseStart_582848 baseEnd_582848 := by
    simpa [prefixWord, tailWord_582848, baseEnd_582848] using wordTrace_append hprefix tailTrace_582848
  have hstable : (prefixWord ++ tailWord_582848).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582848).length < 2 ^ (prefixWord ++ tailWord_582848).sum := by decide
  have hdescent : baseEnd_582848 < baseStart_582848 := by decide
  rcases family_descends (prefixWord ++ tailWord_582848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582910 : List Nat := [4, 2, 2, 1, 1, 2, 4, 5]
def baseStart_582910 : Nat := 118140960795 + 582910 * 2 ^ 59
def prefixEnd_582910 : Nat := 4983230072969 + 3 ^ 40 * 582910 * 2
def baseEnd_582910 : Nat := 44342667898136236391741

theorem tailTrace_582910 : CollatzResearch.WordTrace tailWord_582910 prefixEnd_582910 44342667898136236391741 := by
  unfold tailWord_582910
  simp only [CollatzResearch.WordTrace]
  refine ⟨2657559289778012243410273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14173649545482731964854789 2657559289778012243410273)
  ·
    refine ⟨1993169467333509182557705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2657559289778012243410273 1993169467333509182557705)
    ·
      refine ⟨1494877100500131886918279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1993169467333509182557705 1494877100500131886918279)
      ·
        refine ⟨2242315650750197830377419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1494877100500131886918279 2242315650750197830377419)
        ·
          refine ⟨3363473476125296745566129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2242315650750197830377419 3363473476125296745566129)
          ·
            refine ⟨2522605107093972559174597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3363473476125296745566129 2522605107093972559174597)
            ·
              refine ⟨472988457580119854845237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2522605107093972559174597 472988457580119854845237)
              ·
                refine ⟨44342667898136236391741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 472988457580119854845237 44342667898136236391741)
                ·
                  rfl

theorem cell21_582910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 5].length) (baseStart_582910 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_582910 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_582910 prefixEnd_582910 := by exact prefixLift 582910
  have htrace : WordTrace (prefixWord ++ tailWord_582910) baseStart_582910 baseEnd_582910 := by
    simpa [prefixWord, tailWord_582910, baseEnd_582910] using wordTrace_append hprefix tailTrace_582910
  have hstable : (prefixWord ++ tailWord_582910).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582910).length < 2 ^ (prefixWord ++ tailWord_582910).sum := by decide
  have hdescent : baseEnd_582910 < baseStart_582910 := by decide
  rcases family_descends (prefixWord ++ tailWord_582910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582921 : List Nat := [1, 2, 1, 1, 3, 3, 1, 1, 8]
def baseStart_582921 : Nat := 118140960795 + 582921 * 2 ^ 59
def prefixEnd_582921 : Nat := 4983230072969 + 3 ^ 40 * 582921 * 2
def baseEnd_582921 : Nat := 133030514044275134491867

theorem tailTrace_582921 : CollatzResearch.WordTrace tailWord_582921 prefixEnd_582921 133030514044275134491867 := by
  unfold tailWord_582921
  simp only [CollatzResearch.WordTrace]
  refine ⟨21260875521184246825932617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14173917014122831217288411 21260875521184246825932617)
  ·
    refine ⟨15945656640888185119449463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21260875521184246825932617 15945656640888185119449463)
    ·
      refine ⟨23918484961332277679174195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15945656640888185119449463 23918484961332277679174195)
      ·
        refine ⟨35877727441998416518761293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23918484961332277679174195 35877727441998416518761293)
        ·
          refine ⟨13454147790749406194535485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35877727441998416518761293 13454147790749406194535485)
          ·
            refine ⟨5045305421531027322950807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13454147790749406194535485 5045305421531027322950807)
            ·
              refine ⟨7567958132296540984426211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5045305421531027322950807 7567958132296540984426211)
              ·
                refine ⟨11351937198444811476639317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7567958132296540984426211 11351937198444811476639317)
                ·
                  refine ⟨133030514044275134491867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11351937198444811476639317 133030514044275134491867)
                  ·
                    rfl

theorem cell21_582921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 8].length) (baseStart_582921 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_582921 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_582921 prefixEnd_582921 := by exact prefixLift 582921
  have htrace : WordTrace (prefixWord ++ tailWord_582921) baseStart_582921 baseEnd_582921 := by
    simpa [prefixWord, tailWord_582921, baseEnd_582921] using wordTrace_append hprefix tailTrace_582921
  have hstable : (prefixWord ++ tailWord_582921).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582921).length < 2 ^ (prefixWord ++ tailWord_582921).sum := by decide
  have hdescent : baseEnd_582921 < baseStart_582921 := by decide
  rcases family_descends (prefixWord ++ tailWord_582921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582938 : List Nat := [3, 1, 1, 3, 3, 1, 2, 1, 6]
def baseStart_582938 : Nat := 118140960795 + 582938 * 2 ^ 59
def prefixEnd_582938 : Nat := 4983230072969 + 3 ^ 40 * 582938 * 2
def baseEnd_582938 : Nat := 133034393675886882708499

theorem tailTrace_582938 : CollatzResearch.WordTrace tailWord_582938 prefixEnd_582938 133034393675886882708499 := by
  unfold tailWord_582938
  simp only [CollatzResearch.WordTrace]
  refine ⟨5315373890530664682325367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14174330374748439152867645 5315373890530664682325367)
  ·
    refine ⟨7973060835795997023488051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5315373890530664682325367 7973060835795997023488051)
    ·
      refine ⟨11959591253693995535232077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7973060835795997023488051 11959591253693995535232077)
      ·
        refine ⟨4484846720135248325712029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11959591253693995535232077 4484846720135248325712029)
        ·
          refine ⟨1681817520050718122142011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4484846720135248325712029 1681817520050718122142011)
          ·
            refine ⟨2522726280076077183213017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1681817520050718122142011 2522726280076077183213017)
            ·
              refine ⟨1892044710057057887409763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2522726280076077183213017 1892044710057057887409763)
              ·
                refine ⟨2838067065085586831114645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1892044710057057887409763 2838067065085586831114645)
                ·
                  refine ⟨133034393675886882708499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2838067065085586831114645 133034393675886882708499)
                  ·
                    rfl

theorem cell21_582938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 6].length) (baseStart_582938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_582938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_582938 prefixEnd_582938 := by exact prefixLift 582938
  have htrace : WordTrace (prefixWord ++ tailWord_582938) baseStart_582938 baseEnd_582938 := by
    simpa [prefixWord, tailWord_582938, baseEnd_582938] using wordTrace_append hprefix tailTrace_582938
  have hstable : (prefixWord ++ tailWord_582938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582938).length < 2 ^ (prefixWord ++ tailWord_582938).sum := by decide
  have hdescent : baseEnd_582938 < baseStart_582938 := by decide
  rcases family_descends (prefixWord ++ tailWord_582938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582941 : List Nat := [1, 4, 2, 3, 1, 3, 1, 1, 5]
def baseStart_582941 : Nat := 118140960795 + 582941 * 2 ^ 59
def prefixEnd_582941 : Nat := 4983230072969 + 3 ^ 40 * 582941 * 2
def baseEnd_582941 : Nat := 133035078316759544158493

theorem tailTrace_582941 : CollatzResearch.WordTrace tailWord_582941 prefixEnd_582941 133035078316759544158493 := by
  unfold tailWord_582941
  simp only [CollatzResearch.WordTrace]
  refine ⟨21261604981111790241660677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14174403320741193494440451 21261604981111790241660677)
  ·
    refine ⟨3986550933958460670311377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21261604981111790241660677 3986550933958460670311377)
    ·
      refine ⟨2989913200468845502733533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3986550933958460670311377 2989913200468845502733533)
      ·
        refine ⟨1121217450175817063525075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2989913200468845502733533 1121217450175817063525075)
        ·
          refine ⟨1681826175263725595287613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1121217450175817063525075 1681826175263725595287613)
          ·
            refine ⟨630684815723897098232855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1681826175263725595287613 630684815723897098232855)
            ·
              refine ⟨946027223585845647349283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 630684815723897098232855 946027223585845647349283)
              ·
                refine ⟨1419040835378768471023925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 946027223585845647349283 1419040835378768471023925)
                ·
                  refine ⟨133035078316759544158493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1419040835378768471023925 133035078316759544158493)
                  ·
                    rfl

theorem cell21_582941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 1, 5].length) (baseStart_582941 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_582941 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_582941 prefixEnd_582941 := by exact prefixLift 582941
  have htrace : WordTrace (prefixWord ++ tailWord_582941) baseStart_582941 baseEnd_582941 := by
    simpa [prefixWord, tailWord_582941, baseEnd_582941] using wordTrace_append hprefix tailTrace_582941
  have hstable : (prefixWord ++ tailWord_582941).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582941).length < 2 ^ (prefixWord ++ tailWord_582941).sum := by decide
  have hdescent : baseEnd_582941 < baseStart_582941 := by decide
  rcases family_descends (prefixWord ++ tailWord_582941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582989 : List Nat := [1, 6, 1, 3, 1, 1, 2, 2, 4]
def baseStart_582989 : Nat := 118140960795 + 582989 * 2 ^ 59
def prefixEnd_582989 : Nat := 4983230072969 + 3 ^ 40 * 582989 * 2
def baseEnd_582989 : Nat := 133046032570722127358395

theorem tailTrace_582989 : CollatzResearch.WordTrace tailWord_582989 prefixEnd_582989 133046032570722127358395 := by
  unfold tailWord_582989
  simp only [CollatzResearch.WordTrace]
  refine ⟨21263355684937894439408021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14175570456625262959605347 21263355684937894439408021)
  ·
    refine ⟨996719797731463801847251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 21263355684937894439408021 996719797731463801847251)
    ·
      refine ⟨1495079696597195702770877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 996719797731463801847251 1495079696597195702770877)
      ·
        refine ⟨560654886223948388539079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1495079696597195702770877 560654886223948388539079)
        ·
          refine ⟨840982329335922582808619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 560654886223948388539079 840982329335922582808619)
          ·
            refine ⟨1261473494003883874212929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 840982329335922582808619 1261473494003883874212929)
            ·
              refine ⟨946105120502912905659697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1261473494003883874212929 946105120502912905659697)
              ·
                refine ⟨709578840377184679244773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 946105120502912905659697 709578840377184679244773)
                ·
                  refine ⟨133046032570722127358395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 709578840377184679244773 133046032570722127358395)
                  ·
                    rfl

theorem cell21_582989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_582989 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_582989 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_582989 prefixEnd_582989 := by exact prefixLift 582989
  have htrace : WordTrace (prefixWord ++ tailWord_582989) baseStart_582989 baseEnd_582989 := by
    simpa [prefixWord, tailWord_582989, baseEnd_582989] using wordTrace_append hprefix tailTrace_582989
  have hstable : (prefixWord ++ tailWord_582989).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582989).length < 2 ^ (prefixWord ++ tailWord_582989).sum := by decide
  have hdescent : baseEnd_582989 < baseStart_582989 := by decide
  rcases family_descends (prefixWord ++ tailWord_582989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583000 : List Nat := [2, 1, 2, 2, 1, 1, 5, 4, 3]
def baseStart_583000 : Nat := 118140960795 + 583000 * 2 ^ 59
def prefixEnd_583000 : Nat := 4983230072969 + 3 ^ 40 * 583000 * 2
def baseEnd_583000 : Nat := 133048542920588552675039

theorem tailTrace_583000 : CollatzResearch.WordTrace tailWord_583000 prefixEnd_583000 133048542920588552675039 := by
  unfold tailWord_583000
  simp only [CollatzResearch.WordTrace]
  refine ⟨10631878443949021659029227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14175837925265362212038969 10631878443949021659029227)
  ·
    refine ⟨15947817665923532488543841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10631878443949021659029227 15947817665923532488543841)
    ·
      refine ⟨11960863249442649366407881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15947817665923532488543841 11960863249442649366407881)
      ·
        refine ⟨8970647437081987024805911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11960863249442649366407881 8970647437081987024805911)
        ·
          refine ⟨13455971155622980537208867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8970647437081987024805911 13455971155622980537208867)
          ·
            refine ⟨20183956733434470805813301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13455971155622980537208867 20183956733434470805813301)
            ·
              refine ⟨1892245943759481638044997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20183956733434470805813301 1892245943759481638044997)
              ·
                refine ⟨354796114454902807133437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1892245943759481638044997 354796114454902807133437)
                ·
                  refine ⟨133048542920588552675039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 354796114454902807133437 133048542920588552675039)
                  ·
                    rfl

theorem cell21_583000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 4, 3].length) (baseStart_583000 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_583000 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_583000 prefixEnd_583000 := by exact prefixLift 583000
  have htrace : WordTrace (prefixWord ++ tailWord_583000) baseStart_583000 baseEnd_583000 := by
    simpa [prefixWord, tailWord_583000, baseEnd_583000] using wordTrace_append hprefix tailTrace_583000
  have hstable : (prefixWord ++ tailWord_583000).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583000).length < 2 ^ (prefixWord ++ tailWord_583000).sum := by decide
  have hdescent : baseEnd_583000 < baseStart_583000 := by decide
  rcases family_descends (prefixWord ++ tailWord_583000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583093 : List Nat := [1, 3, 3, 2, 2, 1, 3, 3, 3]
def baseStart_583093 : Nat := 118140960795 + 583093 * 2 ^ 59
def prefixEnd_583093 : Nat := 4983230072969 + 3 ^ 40 * 583093 * 2
def baseEnd_583093 : Nat := 133069766787641057624849

theorem tailTrace_583093 : CollatzResearch.WordTrace tailWord_583093 prefixEnd_583093 133069766787641057624849 := by
  unfold tailWord_583093
  simp only [CollatzResearch.WordTrace]
  refine ⟨21267148876561120201193933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14178099251040746800795955 21267148876561120201193933)
  ·
    refine ⟨7975180828710420075447725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21267148876561120201193933 7975180828710420075447725)
    ·
      refine ⟨2990692810766407528292897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7975180828710420075447725 2990692810766407528292897)
      ·
        refine ⟨2243019608074805646219673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2990692810766407528292897 2243019608074805646219673)
        ·
          refine ⟨1682264706056104234664755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2243019608074805646219673 1682264706056104234664755)
          ·
            refine ⟨2523397059084156351997133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1682264706056104234664755 2523397059084156351997133)
            ·
              refine ⟨946273897156558631998925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2523397059084156351997133 946273897156558631998925)
              ·
                refine ⟨354852711433709486999597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 946273897156558631998925 354852711433709486999597)
                ·
                  refine ⟨133069766787641057624849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 354852711433709486999597 133069766787641057624849)
                  ·
                    rfl

theorem cell21_583093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 3, 3].length) (baseStart_583093 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_583093 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_583093 prefixEnd_583093 := by exact prefixLift 583093
  have htrace : WordTrace (prefixWord ++ tailWord_583093) baseStart_583093 baseEnd_583093 := by
    simpa [prefixWord, tailWord_583093, baseEnd_583093] using wordTrace_append hprefix tailTrace_583093
  have hstable : (prefixWord ++ tailWord_583093).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583093).length < 2 ^ (prefixWord ++ tailWord_583093).sum := by decide
  have hdescent : baseEnd_583093 < baseStart_583093 := by decide
  rcases family_descends (prefixWord ++ tailWord_583093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583169 : List Nat := [1, 2, 4, 1, 4, 1, 1, 4, 3]
def baseStart_583169 : Nat := 118140960795 + 583169 * 2 ^ 59
def prefixEnd_583169 : Nat := 4983230072969 + 3 ^ 40 * 583169 * 2
def baseEnd_583169 : Nat := 133087111023081814358027

theorem tailTrace_583169 : CollatzResearch.WordTrace tailWord_583169 prefixEnd_583169 133087111023081814358027 := by
  unfold tailWord_583169
  simp only [CollatzResearch.WordTrace]
  refine ⟨21269920824285785180960561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14179947216190523453973707 21269920824285785180960561)
  ·
    refine ⟨15952440618214338885720421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21269920824285785180960561 15952440618214338885720421)
    ·
      refine ⟨2991082615915188541072579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15952440618214338885720421 2991082615915188541072579)
      ·
        refine ⟨4486623923872782811608869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2991082615915188541072579 4486623923872782811608869)
        ·
          refine ⟨841241985726146777176663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4486623923872782811608869 841241985726146777176663)
          ·
            refine ⟨1261862978589220165764995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 841241985726146777176663 1261862978589220165764995)
            ·
              refine ⟨1892794467883830248647493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1261862978589220165764995 1892794467883830248647493)
              ·
                refine ⟨354898962728218171621405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1892794467883830248647493 354898962728218171621405)
                ·
                  refine ⟨133087111023081814358027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 354898962728218171621405 133087111023081814358027)
                  ·
                    rfl

theorem cell21_583169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 4, 3].length) (baseStart_583169 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_583169 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_583169 prefixEnd_583169 := by exact prefixLift 583169
  have htrace : WordTrace (prefixWord ++ tailWord_583169) baseStart_583169 baseEnd_583169 := by
    simpa [prefixWord, tailWord_583169, baseEnd_583169] using wordTrace_append hprefix tailTrace_583169
  have hstable : (prefixWord ++ tailWord_583169).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583169).length < 2 ^ (prefixWord ++ tailWord_583169).sum := by decide
  have hdescent : baseEnd_583169 < baseStart_583169 := by decide
  rcases family_descends (prefixWord ++ tailWord_583169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583197 : List Nat := [1, 4, 2, 2, 1, 1, 5, 5]
def baseStart_583197 : Nat := 118140960795 + 583197 * 2 ^ 59
def prefixEnd_583197 : Nat := 4983230072969 + 3 ^ 40 * 583197 * 2
def baseEnd_583197 : Nat := 44364500334853329297101

theorem tailTrace_583197 : CollatzResearch.WordTrace tailWord_583197 prefixEnd_583197 44364500334853329297101 := by
  unfold tailWord_583197
  simp only [CollatzResearch.WordTrace]
  refine ⟨21270942068184345962979845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14180628045456230641986563 21270942068184345962979845)
  ·
    refine ⟨3988301637784564868058721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21270942068184345962979845 3988301637784564868058721)
    ·
      refine ⟨2991226228338423651044041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3988301637784564868058721 2991226228338423651044041)
      ·
        refine ⟨2243419671253817738283031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2991226228338423651044041 2243419671253817738283031)
        ·
          refine ⟨3365129506880726607424547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2243419671253817738283031 3365129506880726607424547)
          ·
            refine ⟨5047694260321089911136821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3365129506880726607424547 5047694260321089911136821)
            ·
              refine ⟨473221336905102179169077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5047694260321089911136821 473221336905102179169077)
              ·
                refine ⟨44364500334853329297101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 473221336905102179169077 44364500334853329297101)
                ·
                  rfl

theorem cell21_583197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 5].length) (baseStart_583197 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_583197 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_583197 prefixEnd_583197 := by exact prefixLift 583197
  have htrace : WordTrace (prefixWord ++ tailWord_583197) baseStart_583197 baseEnd_583197 := by
    simpa [prefixWord, tailWord_583197, baseEnd_583197] using wordTrace_append hprefix tailTrace_583197
  have hstable : (prefixWord ++ tailWord_583197).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583197).length < 2 ^ (prefixWord ++ tailWord_583197).sum := by decide
  have hdescent : baseEnd_583197 < baseStart_583197 := by decide
  rcases family_descends (prefixWord ++ tailWord_583197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583228 : List Nat := [2, 2, 2, 2, 4, 1, 2, 1, 5]
def baseStart_583228 : Nat := 118140960795 + 583228 * 2 ^ 59
def prefixEnd_583228 : Nat := 4983230072969 + 3 ^ 40 * 583228 * 2
def baseEnd_583228 : Nat := 133100575626910822874573

theorem tailTrace_583228 : CollatzResearch.WordTrace tailWord_583228 prefixEnd_583228 133100575626910822874573 := by
  unfold tailWord_583228
  simp only [CollatzResearch.WordTrace]
  refine ⟨10636036365536019128679169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14181381820714692171572225 10636036365536019128679169)
  ·
    refine ⟨7977027274152014346509377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10636036365536019128679169 7977027274152014346509377)
    ·
      refine ⟨5982770455614010759882033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7977027274152014346509377 5982770455614010759882033)
      ·
        refine ⟨4487077841710508069911525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5982770455614010759882033 4487077841710508069911525)
        ·
          refine ⟨841327095320720263108411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4487077841710508069911525 841327095320720263108411)
          ·
            refine ⟨1261990642981080394662617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 841327095320720263108411 1261990642981080394662617)
            ·
              refine ⟨946492982235810295996963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1261990642981080394662617 946492982235810295996963)
              ·
                refine ⟨1419739473353715443995445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 946492982235810295996963 1419739473353715443995445)
                ·
                  refine ⟨133100575626910822874573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1419739473353715443995445 133100575626910822874573)
                  ·
                    rfl

theorem cell21_583228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 1, 5].length) (baseStart_583228 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_583228 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_583228 prefixEnd_583228 := by exact prefixLift 583228
  have htrace : WordTrace (prefixWord ++ tailWord_583228) baseStart_583228 baseEnd_583228 := by
    simpa [prefixWord, tailWord_583228, baseEnd_583228] using wordTrace_append hprefix tailTrace_583228
  have hstable : (prefixWord ++ tailWord_583228).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583228).length < 2 ^ (prefixWord ++ tailWord_583228).sum := by decide
  have hdescent : baseEnd_583228 < baseStart_583228 := by decide
  rcases family_descends (prefixWord ++ tailWord_583228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583391 : List Nat := [1, 1, 2, 3, 2, 2, 10]
def baseStart_583391 : Nat := 118140960795 + 583391 * 2 ^ 59
def prefixEnd_583391 : Nat := 4983230072969 + 3 ^ 40 * 583391 * 2
def baseEnd_583391 : Nat := 14793086049739862406397

theorem tailTrace_583391 : CollatzResearch.WordTrace tailWord_583391 prefixEnd_583391 14793086049739862406397 := by
  unfold tailWord_583391
  simp only [CollatzResearch.WordTrace]
  refine ⟨21278017829481517095542027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14185345219654344730361351 21278017829481517095542027)
  ·
    refine ⟨31917026744222275643313041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21278017829481517095542027 31917026744222275643313041)
    ·
      refine ⟨23937770058166706732484781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31917026744222275643313041 23937770058166706732484781)
      ·
        refine ⟨8976663771812515024681793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23937770058166706732484781 8976663771812515024681793)
        ·
          refine ⟨6732497828859386268511345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8976663771812515024681793 6732497828859386268511345)
          ·
            refine ⟨5049373371644539701383509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6732497828859386268511345 5049373371644539701383509)
            ·
              refine ⟨14793086049739862406397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5049373371644539701383509 14793086049739862406397)
              ·
                rfl

theorem cell21_583391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 10].length) (baseStart_583391 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_583391 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_583391 prefixEnd_583391 := by exact prefixLift 583391
  have htrace : WordTrace (prefixWord ++ tailWord_583391) baseStart_583391 baseEnd_583391 := by
    simpa [prefixWord, tailWord_583391, baseEnd_583391] using wordTrace_append hprefix tailTrace_583391
  have hstable : (prefixWord ++ tailWord_583391).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583391).length < 2 ^ (prefixWord ++ tailWord_583391).sum := by decide
  have hdescent : baseEnd_583391 < baseStart_583391 := by decide
  rcases family_descends (prefixWord ++ tailWord_583391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583439 : List Nat := [1, 1, 2, 1, 1, 1, 4, 7, 3]
def baseStart_583439 : Nat := 118140960795 + 583439 * 2 ^ 59
def prefixEnd_583439 : Nat := 4983230072969 + 3 ^ 40 * 583439 * 2
def baseEnd_583439 : Nat := 133148728701621344857475

theorem tailTrace_583439 : CollatzResearch.WordTrace tailWord_583439 prefixEnd_583439 133148728701621344857475 := by
  unfold tailWord_583439
  simp only [CollatzResearch.WordTrace]
  refine ⟨21279768533307621293289371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14186512355538414195526247 21279768533307621293289371)
  ·
    refine ⟨31919652799961431939934057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21279768533307621293289371 31919652799961431939934057)
    ·
      refine ⟨23939739599971073954950543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31919652799961431939934057 23939739599971073954950543)
      ·
        refine ⟨35909609399956610932425815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23939739599971073954950543 35909609399956610932425815)
        ·
          refine ⟨53864414099934916398638723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35909609399956610932425815 53864414099934916398638723)
          ·
            refine ⟨80796621149902374597958085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53864414099934916398638723 80796621149902374597958085)
            ·
              refine ⟨15149366465606695237117141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80796621149902374597958085 15149366465606695237117141)
              ·
                refine ⟨355063276537656919619933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 15149366465606695237117141 355063276537656919619933)
                ·
                  refine ⟨133148728701621344857475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 355063276537656919619933 133148728701621344857475)
                  ·
                    rfl

theorem cell21_583439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 7, 3].length) (baseStart_583439 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_583439 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_583439 prefixEnd_583439 := by exact prefixLift 583439
  have htrace : WordTrace (prefixWord ++ tailWord_583439) baseStart_583439 baseEnd_583439 := by
    simpa [prefixWord, tailWord_583439, baseEnd_583439] using wordTrace_append hprefix tailTrace_583439
  have hstable : (prefixWord ++ tailWord_583439).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583439).length < 2 ^ (prefixWord ++ tailWord_583439).sum := by decide
  have hdescent : baseEnd_583439 < baseStart_583439 := by decide
  rcases family_descends (prefixWord ++ tailWord_583439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583560 : List Nat := [2, 1, 3, 3, 3, 1, 8]
def baseStart_583560 : Nat := 118140960795 + 583560 * 2 ^ 59
def prefixEnd_583560 : Nat := 4983230072969 + 3 ^ 40 * 583560 * 2
def baseEnd_583560 : Nat := 14797371394461335926729

theorem tailTrace_583560 : CollatzResearch.WordTrace tailWord_583560 prefixEnd_583560 14797371394461335926729 := by
  unfold tailWord_583560
  simp only [CollatzResearch.WordTrace]
  refine ⟨10642090882934629479222067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14189454510579505972296089 10642090882934629479222067)
  ·
    refine ⟨15963136324401944218833101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10642090882934629479222067 15963136324401944218833101)
    ·
      refine ⟨5986176121650729082062413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15963136324401944218833101 5986176121650729082062413)
      ·
        refine ⟨2244816045619023405773405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5986176121650729082062413 2244816045619023405773405)
        ·
          refine ⟨841806017107133777165027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2244816045619023405773405 841806017107133777165027)
          ·
            refine ⟨1262709025660700665747541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 841806017107133777165027 1262709025660700665747541)
            ·
              refine ⟨14797371394461335926729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1262709025660700665747541 14797371394461335926729)
              ·
                rfl

theorem cell21_583560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 8].length) (baseStart_583560 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_583560 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_583560 prefixEnd_583560 := by exact prefixLift 583560
  have htrace : WordTrace (prefixWord ++ tailWord_583560) baseStart_583560 baseEnd_583560 := by
    simpa [prefixWord, tailWord_583560, baseEnd_583560] using wordTrace_append hprefix tailTrace_583560
  have hstable : (prefixWord ++ tailWord_583560).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583560).length < 2 ^ (prefixWord ++ tailWord_583560).sum := by decide
  have hdescent : baseEnd_583560 < baseStart_583560 := by decide
  rcases family_descends (prefixWord ++ tailWord_583560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583591 : List Nat := [1, 1, 6, 1, 2, 1, 2, 2, 5]
def baseStart_583591 : Nat := 118140960795 + 583591 * 2 ^ 59
def prefixEnd_583591 : Nat := 4983230072969 + 3 ^ 40 * 583591 * 2
def baseEnd_583591 : Nat := 133183417172502858323831

theorem tailTrace_583591 : CollatzResearch.WordTrace tailWord_583591 prefixEnd_583591 133183417172502858323831 := by
  unfold tailWord_583591
  simp only [CollatzResearch.WordTrace]
  refine ⟨21285312428756951252822627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14190208285837967501881751 21285312428756951252822627)
  ·
    refine ⟨31927968643135426879233941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21285312428756951252822627 31927968643135426879233941)
    ·
      refine ⟨1496623530146973134964091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 31927968643135426879233941 1496623530146973134964091)
      ·
        refine ⟨2244935295220459702446137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1496623530146973134964091 2244935295220459702446137)
        ·
          refine ⟨1683701471415344776834603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2244935295220459702446137 1683701471415344776834603)
          ·
            refine ⟨2525552207123017165251905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1683701471415344776834603 2525552207123017165251905)
            ·
              refine ⟨1894164155342262873938929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2525552207123017165251905 1894164155342262873938929)
              ·
                refine ⟨1420623116506697155454197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1894164155342262873938929 1420623116506697155454197)
                ·
                  refine ⟨133183417172502858323831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1420623116506697155454197 133183417172502858323831)
                  ·
                    rfl

theorem cell21_583591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 2, 5].length) (baseStart_583591 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_583591 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_583591 prefixEnd_583591 := by exact prefixLift 583591
  have htrace : WordTrace (prefixWord ++ tailWord_583591) baseStart_583591 baseEnd_583591 := by
    simpa [prefixWord, tailWord_583591, baseEnd_583591] using wordTrace_append hprefix tailTrace_583591
  have hstable : (prefixWord ++ tailWord_583591).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583591).length < 2 ^ (prefixWord ++ tailWord_583591).sum := by decide
  have hdescent : baseEnd_583591 < baseStart_583591 := by decide
  rcases family_descends (prefixWord ++ tailWord_583591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583605 : List Nat := [1, 3, 3, 2, 1, 2, 1, 2, 6]
def baseStart_583605 : Nat := 118140960795 + 583605 * 2 ^ 59
def prefixEnd_583605 : Nat := 4983230072969 + 3 ^ 40 * 583605 * 2
def baseEnd_583605 : Nat := 133186612163241945090469

theorem tailTrace_583605 : CollatzResearch.WordTrace tailWord_583605 prefixEnd_583605 133186612163241945090469 := by
  unfold tailWord_583605
  simp only [CollatzResearch.WordTrace]
  refine ⟨21285823050706231643832269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14190548700470821095888179 21285823050706231643832269)
  ·
    refine ⟨7982183644014836866437101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21285823050706231643832269 7982183644014836866437101)
    ·
      refine ⟨2993318866505563824913913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7982183644014836866437101 2993318866505563824913913)
      ·
        refine ⟨2244989149879172868685435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2993318866505563824913913 2244989149879172868685435)
        ·
          refine ⟨3367483724818759303028153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2244989149879172868685435 3367483724818759303028153)
          ·
            refine ⟨2525612793614069477271115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3367483724818759303028153 2525612793614069477271115)
            ·
              refine ⟨3788419190421104215906673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2525612793614069477271115 3788419190421104215906673)
              ·
                refine ⟨2841314392815828161930005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3788419190421104215906673 2841314392815828161930005)
                ·
                  refine ⟨133186612163241945090469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2841314392815828161930005 133186612163241945090469)
                  ·
                    rfl

theorem cell21_583605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 6].length) (baseStart_583605 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_583605 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_583605 prefixEnd_583605 := by exact prefixLift 583605
  have htrace : WordTrace (prefixWord ++ tailWord_583605) baseStart_583605 baseEnd_583605 := by
    simpa [prefixWord, tailWord_583605, baseEnd_583605] using wordTrace_append hprefix tailTrace_583605
  have hstable : (prefixWord ++ tailWord_583605).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583605).length < 2 ^ (prefixWord ++ tailWord_583605).sum := by decide
  have hdescent : baseEnd_583605 < baseStart_583605 := by decide
  rcases family_descends (prefixWord ++ tailWord_583605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583636 : List Nat := [2, 4, 1, 2, 1, 1, 4, 6]
def baseStart_583636 : Nat := 118140960795 + 583636 * 2 ^ 59
def prefixEnd_583636 : Nat := 4983230072969 + 3 ^ 40 * 583636 * 2
def baseEnd_583636 : Nat := 44397895595197593357913

theorem tailTrace_583636 : CollatzResearch.WordTrace tailWord_583636 prefixEnd_583636 44397895595197593357913 := by
  unfold tailWord_583636
  simp only [CollatzResearch.WordTrace]
  refine ⟨10643476856796961969105381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14191302475729282625473841 10643476856796961969105381)
  ·
    refine ⟨1995651910649430369207259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10643476856796961969105381 1995651910649430369207259)
    ·
      refine ⟨2993477865974145553810889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1995651910649430369207259 2993477865974145553810889)
      ·
        refine ⟨2245108399480609165358167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2993477865974145553810889 2245108399480609165358167)
        ·
          refine ⟨3367662599220913748037251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2245108399480609165358167 3367662599220913748037251)
          ·
            refine ⟨5051493898831370622055877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3367662599220913748037251 5051493898831370622055877)
            ·
              refine ⟨947155106030881991635477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5051493898831370622055877 947155106030881991635477)
              ·
                refine ⟨44397895595197593357913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 947155106030881991635477 44397895595197593357913)
                ·
                  rfl

theorem cell21_583636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 6].length) (baseStart_583636 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_583636 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_583636 prefixEnd_583636 := by exact prefixLift 583636
  have htrace : WordTrace (prefixWord ++ tailWord_583636) baseStart_583636 baseEnd_583636 := by
    simpa [prefixWord, tailWord_583636, baseEnd_583636] using wordTrace_append hprefix tailTrace_583636
  have hstable : (prefixWord ++ tailWord_583636).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583636).length < 2 ^ (prefixWord ++ tailWord_583636).sum := by decide
  have hdescent : baseEnd_583636 < baseStart_583636 := by decide
  rcases family_descends (prefixWord ++ tailWord_583636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583664 : List Nat := [2, 1, 1, 1, 3, 2, 2, 1, 8]
def baseStart_583664 : Nat := 118140960795 + 583664 * 2 ^ 59
def prefixEnd_583664 : Nat := 4983230072969 + 3 ^ 40 * 583664 * 2
def baseEnd_583664 : Nat := 133200076767070953607015

theorem tailTrace_583664 : CollatzResearch.WordTrace tailWord_583664 prefixEnd_583664 133200076767070953607015 := by
  unfold tailWord_583664
  simp only [CollatzResearch.WordTrace]
  refine ⟨10643987478746242360115023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14191983304994989813486697 10643987478746242360115023)
  ·
    refine ⟨15965981218119363540172535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10643987478746242360115023 15965981218119363540172535)
    ·
      refine ⟨23948971827179045310258803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15965981218119363540172535 23948971827179045310258803)
      ·
        refine ⟨35923457740768567965388205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23948971827179045310258803 35923457740768567965388205)
        ·
          refine ⟨13471296652788212987020577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35923457740768567965388205 13471296652788212987020577)
          ·
            refine ⟨10103472489591159740265433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13471296652788212987020577 10103472489591159740265433)
            ·
              refine ⟨7577604367193369805199075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10103472489591159740265433 7577604367193369805199075)
              ·
                refine ⟨11366406550790054707798613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7577604367193369805199075 11366406550790054707798613)
                ·
                  refine ⟨133200076767070953607015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11366406550790054707798613 133200076767070953607015)
                  ·
                    rfl

theorem cell21_583664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 8].length) (baseStart_583664 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_583664 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_583664 prefixEnd_583664 := by exact prefixLift 583664
  have htrace : WordTrace (prefixWord ++ tailWord_583664) baseStart_583664 baseEnd_583664 := by
    simpa [prefixWord, tailWord_583664, baseEnd_583664] using wordTrace_append hprefix tailTrace_583664
  have hstable : (prefixWord ++ tailWord_583664).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583664).length < 2 ^ (prefixWord ++ tailWord_583664).sum := by decide
  have hdescent : baseEnd_583664 < baseStart_583664 := by decide
  rcases family_descends (prefixWord ++ tailWord_583664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583732 : List Nat := [2, 5, 1, 2, 2, 2, 1, 2, 4]
def baseStart_583732 : Nat := 118140960795 + 583732 * 2 ^ 59
def prefixEnd_583732 : Nat := 4983230072969 + 3 ^ 40 * 583732 * 2
def baseEnd_583732 : Nat := 133215595293517946473543

theorem tailTrace_583732 : CollatzResearch.WordTrace tailWord_583732 prefixEnd_583732 133215595293517946473543 := by
  unfold tailWord_583732
  simp only [CollatzResearch.WordTrace]
  refine ⟨10645227560623066166852725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14193636747497421555803633 10645227560623066166852725)
  ·
    refine ⟨997990083808412453142443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10645227560623066166852725 997990083808412453142443)
    ·
      refine ⟨1496985125712618679713665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 997990083808412453142443 1496985125712618679713665)
      ·
        refine ⟨1122738844284464009785249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1496985125712618679713665 1122738844284464009785249)
        ·
          refine ⟨842054133213348007338937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1122738844284464009785249 842054133213348007338937)
          ·
            refine ⟨631540599910011005504203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 842054133213348007338937 631540599910011005504203)
            ·
              refine ⟨947310899865016508256305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 631540599910011005504203 947310899865016508256305)
              ·
                refine ⟨710483174898762381192229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 947310899865016508256305 710483174898762381192229)
                ·
                  refine ⟨133215595293517946473543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 710483174898762381192229 133215595293517946473543)
                  ·
                    rfl

theorem cell21_583732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_583732 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_583732 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_583732 prefixEnd_583732 := by exact prefixLift 583732
  have htrace : WordTrace (prefixWord ++ tailWord_583732) baseStart_583732 baseEnd_583732 := by
    simpa [prefixWord, tailWord_583732, baseEnd_583732] using wordTrace_append hprefix tailTrace_583732
  have hstable : (prefixWord ++ tailWord_583732).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583732).length < 2 ^ (prefixWord ++ tailWord_583732).sum := by decide
  have hdescent : baseEnd_583732 < baseStart_583732 := by decide
  rcases family_descends (prefixWord ++ tailWord_583732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583743 : List Nat := [1, 1, 2, 2, 3, 1, 4, 4, 3]
def baseStart_583743 : Nat := 118140960795 + 583743 * 2 ^ 59
def prefixEnd_583743 : Nat := 4983230072969 + 3 ^ 40 * 583743 * 2
def baseEnd_583743 : Nat := 133218105643384371790187

theorem tailTrace_583743 : CollatzResearch.WordTrace tailWord_583743 prefixEnd_583743 133218105643384371790187 := by
  unfold tailWord_583743
  simp only [CollatzResearch.WordTrace]
  refine ⟨21290856324206281212355883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14193904216137520808237255 21290856324206281212355883)
  ·
    refine ⟨31936284486309421818533825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21290856324206281212355883 31936284486309421818533825)
    ·
      refine ⟨23952213364732066363900369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31936284486309421818533825 23952213364732066363900369)
      ·
        refine ⟨17964160023549049772925277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23952213364732066363900369 17964160023549049772925277)
        ·
          refine ⟨6736560008830893664846979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17964160023549049772925277 6736560008830893664846979)
          ·
            refine ⟨10104840013246340497270469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6736560008830893664846979 10104840013246340497270469)
            ·
              refine ⟨1894657502483688843238213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10104840013246340497270469 1894657502483688843238213)
              ·
                refine ⟨355248281715691658107165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1894657502483688843238213 355248281715691658107165)
                ·
                  refine ⟨133218105643384371790187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 355248281715691658107165 133218105643384371790187)
                  ·
                    rfl

theorem cell21_583743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 4, 3].length) (baseStart_583743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_583743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_583743 prefixEnd_583743 := by exact prefixLift 583743
  have htrace : WordTrace (prefixWord ++ tailWord_583743) baseStart_583743 baseEnd_583743 := by
    simpa [prefixWord, tailWord_583743, baseEnd_583743] using wordTrace_append hprefix tailTrace_583743
  have hstable : (prefixWord ++ tailWord_583743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583743).length < 2 ^ (prefixWord ++ tailWord_583743).sum := by decide
  have hdescent : baseEnd_583743 < baseStart_583743 := by decide
  rcases family_descends (prefixWord ++ tailWord_583743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583847 : List Nat := [1, 1, 6, 2, 11]
def baseStart_583847 : Nat := 118140960795 + 583847 * 2 ^ 59
def prefixEnd_583847 : Nat := 4983230072969 + 3 ^ 40 * 583847 * 2
def baseEnd_583847 : Nat := 1644960985929670395761

theorem tailTrace_583847 : CollatzResearch.WordTrace tailWord_583847 prefixEnd_583847 1644960985929670395761 := by
  unfold tailWord_583847
  simp only [CollatzResearch.WordTrace]
  refine ⟨21294649515829506974141795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14196433010553004649427863 21294649515829506974141795)
  ·
    refine ⟨31941974273744260461212693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21294649515829506974141795 31941974273744260461212693)
    ·
      refine ⟨1497280044081762209119345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 31941974273744260461212693 1497280044081762209119345)
      ·
        refine ⟨1122960033061321656839509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1497280044081762209119345 1122960033061321656839509)
        ·
          refine ⟨1644960985929670395761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1122960033061321656839509 1644960985929670395761)
          ·
            rfl

theorem cell21_583847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 11].length) (baseStart_583847 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_583847 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_583847 prefixEnd_583847 := by exact prefixLift 583847
  have htrace : WordTrace (prefixWord ++ tailWord_583847) baseStart_583847 baseEnd_583847 := by
    simpa [prefixWord, tailWord_583847, baseEnd_583847] using wordTrace_append hprefix tailTrace_583847
  have hstable : (prefixWord ++ tailWord_583847).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583847).length < 2 ^ (prefixWord ++ tailWord_583847).sum := by decide
  have hdescent : baseEnd_583847 < baseStart_583847 := by decide
  rcases family_descends (prefixWord ++ tailWord_583847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583853 : List Nat := [1, 5, 2, 1, 2, 1, 4, 2, 3]
def baseStart_583853 : Nat := 118140960795 + 583853 * 2 ^ 59
def prefixEnd_583853 : Nat := 4983230072969 + 3 ^ 40 * 583853 * 2
def baseEnd_583853 : Nat := 133243209142048624956629

theorem tailTrace_583853 : CollatzResearch.WordTrace tailWord_583853 prefixEnd_583853 133243209142048624956629 := by
  unfold tailWord_583853
  simp only [CollatzResearch.WordTrace]
  refine ⟨21294868353807769998860213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14196578902538513332573475 21294868353807769998860213)
  ·
    refine ⟨1996393908169478437393145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21294868353807769998860213 1996393908169478437393145)
    ·
      refine ⟨1497295431127108828044859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1996393908169478437393145 1497295431127108828044859)
      ·
        refine ⟨2245943146690663242067289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1497295431127108828044859 2245943146690663242067289)
        ·
          refine ⟨1684457360017997431550467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2245943146690663242067289 1684457360017997431550467)
          ·
            refine ⟨2526686040026996147325701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1684457360017997431550467 2526686040026996147325701)
            ·
              refine ⟨473753632505061777623569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2526686040026996147325701 473753632505061777623569)
              ·
                refine ⟨355315224378796333217677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 473753632505061777623569 355315224378796333217677)
                ·
                  refine ⟨133243209142048624956629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 355315224378796333217677 133243209142048624956629)
                  ·
                    rfl

theorem cell21_583853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_583853 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_583853 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_583853 prefixEnd_583853 := by exact prefixLift 583853
  have htrace : WordTrace (prefixWord ++ tailWord_583853) baseStart_583853 baseEnd_583853 := by
    simpa [prefixWord, tailWord_583853, baseEnd_583853] using wordTrace_append hprefix tailTrace_583853
  have hstable : (prefixWord ++ tailWord_583853).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583853).length < 2 ^ (prefixWord ++ tailWord_583853).sum := by decide
  have hdescent : baseEnd_583853 < baseStart_583853 := by decide
  rcases family_descends (prefixWord ++ tailWord_583853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583909 : List Nat := [1, 3, 1, 4, 2, 2, 1, 1, 6]
def baseStart_583909 : Nat := 118140960795 + 583909 * 2 ^ 59
def prefixEnd_583909 : Nat := 4983230072969 + 3 ^ 40 * 583909 * 2
def baseEnd_583909 : Nat := 133255989105004972023181

theorem tailTrace_583909 : CollatzResearch.WordTrace tailWord_583909 prefixEnd_583909 133255989105004972023181 := by
  unfold tailWord_583909
  simp only [CollatzResearch.WordTrace]
  refine ⟨21296910841604891562898781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14197940561069927708599187 21296910841604891562898781)
  ·
    refine ⟨7986341565601834336087043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21296910841604891562898781 7986341565601834336087043)
    ·
      refine ⟨11979512348402751504130565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7986341565601834336087043 11979512348402751504130565)
      ·
        refine ⟨2246158565325515907024481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11979512348402751504130565 2246158565325515907024481)
        ·
          refine ⟨1684618923994136930268361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2246158565325515907024481 1684618923994136930268361)
          ·
            refine ⟨1263464192995602697701271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1684618923994136930268361 1263464192995602697701271)
            ·
              refine ⟨1895196289493404046551907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1263464192995602697701271 1895196289493404046551907)
              ·
                refine ⟨2842794434240106069827861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1895196289493404046551907 2842794434240106069827861)
                ·
                  refine ⟨133255989105004972023181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2842794434240106069827861 133255989105004972023181)
                  ·
                    rfl

theorem cell21_583909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 6].length) (baseStart_583909 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_583909 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_583909 prefixEnd_583909 := by exact prefixLift 583909
  have htrace : WordTrace (prefixWord ++ tailWord_583909) baseStart_583909 baseEnd_583909 := by
    simpa [prefixWord, tailWord_583909, baseEnd_583909] using wordTrace_append hprefix tailTrace_583909
  have hstable : (prefixWord ++ tailWord_583909).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583909).length < 2 ^ (prefixWord ++ tailWord_583909).sum := by decide
  have hdescent : baseEnd_583909 < baseStart_583909 := by decide
  rcases family_descends (prefixWord ++ tailWord_583909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583940 : List Nat := [2, 3, 2, 2, 3, 1, 1, 7]
def baseStart_583940 : Nat := 118140960795 + 583940 * 2 ^ 59
def prefixEnd_583940 : Nat := 4983230072969 + 3 ^ 40 * 583940 * 2
def baseEnd_583940 : Nat := 44421021242451935668817

theorem tailTrace_583940 : CollatzResearch.WordTrace tailWord_583940 prefixEnd_583940 44421021242451935668817 := by
  unfold tailWord_583940
  simp only [CollatzResearch.WordTrace]
  refine ⟨10649020752246291928638637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14198694336328389238184849 10649020752246291928638637)
  ·
    refine ⟨3993382782092359473239489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10649020752246291928638637 3993382782092359473239489)
    ·
      refine ⟨2995037086569269604929617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3993382782092359473239489 2995037086569269604929617)
      ·
        refine ⟨2246277814926952203697213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2995037086569269604929617 2246277814926952203697213)
        ·
          refine ⟨842354180597607076386455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2246277814926952203697213 842354180597607076386455)
          ·
            refine ⟨1263531270896410614579683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 842354180597607076386455 1263531270896410614579683)
            ·
              refine ⟨1895296906344615921869525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1263531270896410614579683 1895296906344615921869525)
              ·
                refine ⟨44421021242451935668817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1895296906344615921869525 44421021242451935668817)
                ·
                  rfl

theorem cell21_583940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 7].length) (baseStart_583940 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_583940 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_583940 prefixEnd_583940 := by exact prefixLift 583940
  have htrace : WordTrace (prefixWord ++ tailWord_583940) baseStart_583940 baseEnd_583940 := by
    simpa [prefixWord, tailWord_583940, baseEnd_583940] using wordTrace_append hprefix tailTrace_583940
  have hstable : (prefixWord ++ tailWord_583940).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583940).length < 2 ^ (prefixWord ++ tailWord_583940).sum := by decide
  have hdescent : baseEnd_583940 < baseStart_583940 := by decide
  rcases family_descends (prefixWord ++ tailWord_583940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584078 : List Nat := [4, 1, 1, 4, 1, 1, 3, 2, 4]
def baseStart_584078 : Nat := 118140960795 + 584078 * 2 ^ 59
def prefixEnd_584078 : Nat := 4983230072969 + 3 ^ 40 * 584078 * 2
def baseEnd_584078 : Nat := 133294557207498233706169

theorem tailTrace_584078 : CollatzResearch.WordTrace tailWord_584078 prefixEnd_584078 133294557207498233706169 := by
  unfold tailWord_584078
  simp only [CollatzResearch.WordTrace]
  refine ⟨2662884347249079178225111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14202049851995088950533925 2662884347249079178225111)
  ·
    refine ⟨3994326520873618767337667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2662884347249079178225111 3994326520873618767337667)
    ·
      refine ⟨5991489781310428151006501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3994326520873618767337667 5991489781310428151006501)
      ·
        refine ⟨1123404333995705278313719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5991489781310428151006501 1123404333995705278313719)
        ·
          refine ⟨1685106500993557917470579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1123404333995705278313719 1685106500993557917470579)
          ·
            refine ⟨2527659751490336876205869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1685106500993557917470579 2527659751490336876205869)
            ·
              refine ⟨947872406808876328577201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2527659751490336876205869 947872406808876328577201)
              ·
                refine ⟨710904305106657246432901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 947872406808876328577201 710904305106657246432901)
                ·
                  refine ⟨133294557207498233706169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 710904305106657246432901 133294557207498233706169)
                  ·
                    rfl

theorem cell21_584078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_584078 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_584078 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_584078 prefixEnd_584078 := by exact prefixLift 584078
  have htrace : WordTrace (prefixWord ++ tailWord_584078) baseStart_584078 baseEnd_584078 := by
    simpa [prefixWord, tailWord_584078, baseEnd_584078] using wordTrace_append hprefix tailTrace_584078
  have hstable : (prefixWord ++ tailWord_584078).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584078).length < 2 ^ (prefixWord ++ tailWord_584078).sum := by decide
  have hdescent : baseEnd_584078 < baseStart_584078 := by decide
  rcases family_descends (prefixWord ++ tailWord_584078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584140 : List Nat := [2, 2, 1, 4, 4, 1, 1, 1, 5]
def baseStart_584140 : Nat := 118140960795 + 584140 * 2 ^ 59
def prefixEnd_584140 : Nat := 4983230072969 + 3 ^ 40 * 584140 * 2
def baseEnd_584140 : Nat := 133308706452199903672709

theorem tailTrace_584140 : CollatzResearch.WordTrace tailWord_584140 prefixEnd_584140 133308706452199903672709 := by
  unfold tailWord_584140
  simp only [CollatzResearch.WordTrace]
  refine ⟨10652668051884009007278937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14203557402512012009705249 10652668051884009007278937)
  ·
    refine ⟨7989501038913006755459203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10652668051884009007278937 7989501038913006755459203)
    ·
      refine ⟨11984251558369510133188805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7989501038913006755459203 11984251558369510133188805)
      ·
        refine ⟨2247047167194283149972901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11984251558369510133188805 2247047167194283149972901)
        ·
          refine ⟨421321343848928090619919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2247047167194283149972901 421321343848928090619919)
          ·
            refine ⟨631982015773392135929879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 421321343848928090619919 631982015773392135929879)
            ·
              refine ⟨947973023660088203894819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 631982015773392135929879 947973023660088203894819)
              ·
                refine ⟨1421959535490132305842229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 947973023660088203894819 1421959535490132305842229)
                ·
                  refine ⟨133308706452199903672709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1421959535490132305842229 133308706452199903672709)
                  ·
                    rfl

theorem cell21_584140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 1, 5].length) (baseStart_584140 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_584140 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_584140 prefixEnd_584140 := by exact prefixLift 584140
  have htrace : WordTrace (prefixWord ++ tailWord_584140) baseStart_584140 baseEnd_584140 := by
    simpa [prefixWord, tailWord_584140, baseEnd_584140] using wordTrace_append hprefix tailTrace_584140
  have hstable : (prefixWord ++ tailWord_584140).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584140).length < 2 ^ (prefixWord ++ tailWord_584140).sum := by decide
  have hdescent : baseEnd_584140 < baseStart_584140 := by decide
  rcases family_descends (prefixWord ++ tailWord_584140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584309 : List Nat := [1, 3, 4, 2, 2, 1, 3, 2, 3]
def baseStart_584309 : Nat := 118140960795 + 584309 * 2 ^ 59
def prefixEnd_584309 : Nat := 4983230072969 + 3 ^ 40 * 584309 * 2
def baseEnd_584309 : Nat := 133347274554693165355697

theorem tailTrace_584309 : CollatzResearch.WordTrace tailWord_584309 prefixEnd_584309 133347274554693165355697 := by
  unfold tailWord_584309
  simp only [CollatzResearch.WordTrace]
  refine ⟨21311500040155759877459981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14207666693437173251639987 21311500040155759877459981)
  ·
    refine ⟨7991812515058409954047493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21311500040155759877459981 7991812515058409954047493)
    ·
      refine ⟨1498464846573451866383905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7991812515058409954047493 1498464846573451866383905)
      ·
        refine ⟨1123848634930088899787929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1498464846573451866383905 1123848634930088899787929)
        ·
          refine ⟨842886476197566674840947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1123848634930088899787929 842886476197566674840947)
          ·
            refine ⟨1264329714296350012261421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 842886476197566674840947 1264329714296350012261421)
            ·
              refine ⟨474123642861131254598033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1264329714296350012261421 474123642861131254598033)
              ·
                refine ⟨355592732145848440948525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 474123642861131254598033 355592732145848440948525)
                ·
                  refine ⟨133347274554693165355697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 355592732145848440948525 133347274554693165355697)
                  ·
                    rfl

theorem cell21_584309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 2, 3].length) (baseStart_584309 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_584309 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_584309 prefixEnd_584309 := by exact prefixLift 584309
  have htrace : WordTrace (prefixWord ++ tailWord_584309) baseStart_584309 baseEnd_584309 := by
    simpa [prefixWord, tailWord_584309, baseEnd_584309] using wordTrace_append hprefix tailTrace_584309
  have hstable : (prefixWord ++ tailWord_584309).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584309).length < 2 ^ (prefixWord ++ tailWord_584309).sum := by decide
  have hdescent : baseEnd_584309 < baseStart_584309 := by decide
  rcases family_descends (prefixWord ++ tailWord_584309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584331 : List Nat := [1, 1, 1, 1, 4, 1, 2, 2, 8]
def baseStart_584331 : Nat := 118140960795 + 584331 * 2 ^ 59
def prefixEnd_584331 : Nat := 4983230072969 + 3 ^ 40 * 584331 * 2
def baseEnd_584331 : Nat := 133352295254426015988985

theorem tailTrace_584331 : CollatzResearch.WordTrace tailWord_584331 prefixEnd_584331 133352295254426015988985 := by
  unfold tailWord_584331
  simp only [CollatzResearch.WordTrace]
  refine ⟨21312302446076057634760847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14208201630717371756507231 21312302446076057634760847)
  ·
    refine ⟨31968453669114086452141271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21312302446076057634760847 31968453669114086452141271)
    ·
      refine ⟨47952680503671129678211907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31968453669114086452141271 47952680503671129678211907)
      ·
        refine ⟨71929020755506694517317861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47952680503671129678211907 71929020755506694517317861)
        ·
          refine ⟨13486691391657505221997099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71929020755506694517317861 13486691391657505221997099)
          ·
            refine ⟨20230037087486257832995649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13486691391657505221997099 20230037087486257832995649)
            ·
              refine ⟨15172527815614693374746737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20230037087486257832995649 15172527815614693374746737)
              ·
                refine ⟨11379395861711020031060053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15172527815614693374746737 11379395861711020031060053)
                ·
                  refine ⟨133352295254426015988985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11379395861711020031060053 133352295254426015988985)
                  ·
                    rfl

theorem cell21_584331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 8].length) (baseStart_584331 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_584331 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_584331 prefixEnd_584331 := by exact prefixLift 584331
  have htrace : WordTrace (prefixWord ++ tailWord_584331) baseStart_584331 baseEnd_584331 := by
    simpa [prefixWord, tailWord_584331, baseEnd_584331] using wordTrace_append hprefix tailTrace_584331
  have hstable : (prefixWord ++ tailWord_584331).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584331).length < 2 ^ (prefixWord ++ tailWord_584331).sum := by decide
  have hdescent : baseEnd_584331 < baseStart_584331 := by decide
  rcases family_descends (prefixWord ++ tailWord_584331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584365 : List Nat := [1, 5, 2, 1, 1, 2, 1, 4, 4]
def baseStart_584365 : Nat := 118140960795 + 584365 * 2 ^ 59
def prefixEnd_584365 : Nat := 4983230072969 + 3 ^ 40 * 584365 * 2
def baseEnd_584365 : Nat := 133360054517649512422249

theorem tailTrace_584365 : CollatzResearch.WordTrace tailWord_584365 prefixEnd_584365 133360054517649512422249 := by
  unfold tailWord_584365
  simp only [CollatzResearch.WordTrace]
  refine ⟨21313542527952881441498549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14209028351968587627665699 21313542527952881441498549)
  ·
    refine ⟨1998144611995582635140489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21313542527952881441498549 1998144611995582635140489)
    ·
      refine ⟨1498608458996686976355367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1998144611995582635140489 1498608458996686976355367)
      ·
        refine ⟨2247912688495030464533051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1498608458996686976355367 2247912688495030464533051)
        ·
          refine ⟨3371869032742545696799577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2247912688495030464533051 3371869032742545696799577)
          ·
            refine ⟨2528901774556909272599683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3371869032742545696799577 2528901774556909272599683)
            ·
              refine ⟨3793352661835363908899525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2528901774556909272599683 3793352661835363908899525)
              ·
                refine ⟨711253624094130732918661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3793352661835363908899525 711253624094130732918661)
                ·
                  refine ⟨133360054517649512422249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 711253624094130732918661 133360054517649512422249)
                  ·
                    rfl

theorem cell21_584365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_584365 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_584365 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_584365 prefixEnd_584365 := by exact prefixLift 584365
  have htrace : WordTrace (prefixWord ++ tailWord_584365) baseStart_584365 baseEnd_584365 := by
    simpa [prefixWord, tailWord_584365, baseEnd_584365] using wordTrace_append hprefix tailTrace_584365
  have hstable : (prefixWord ++ tailWord_584365).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584365).length < 2 ^ (prefixWord ++ tailWord_584365).sum := by decide
  have hdescent : baseEnd_584365 < baseStart_584365 := by decide
  rcases family_descends (prefixWord ++ tailWord_584365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584396 : List Nat := [2, 2, 1, 5, 1, 2, 3, 5]
def baseStart_584396 : Nat := 118140960795 + 584396 * 2 ^ 59
def prefixEnd_584396 : Nat := 4983230072969 + 3 ^ 40 * 584396 * 2
def baseEnd_584396 : Nat := 44455709713333449135173

theorem tailTrace_584396 : CollatzResearch.WordTrace tailWord_584396 prefixEnd_584396 44455709713333449135173 := by
  unfold tailWord_584396
  simp only [CollatzResearch.WordTrace]
  refine ⟨10657336595420286867938521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14209782127227049157251361 10657336595420286867938521)
  ·
    refine ⟨7993002446565215150953891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10657336595420286867938521 7993002446565215150953891)
    ·
      refine ⟨11989503669847822726430837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7993002446565215150953891 11989503669847822726430837)
      ·
        refine ⟨1124015969048233380602891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11989503669847822726430837 1124015969048233380602891)
        ·
          refine ⟨1686023953572350070904337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1124015969048233380602891 1686023953572350070904337)
          ·
            refine ⟨1264517965179262553178253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1686023953572350070904337 1264517965179262553178253)
            ·
              refine ⟨474194236942223457441845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1264517965179262553178253 474194236942223457441845)
              ·
                refine ⟨44455709713333449135173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 474194236942223457441845 44455709713333449135173)
                ·
                  rfl

theorem cell21_584396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 5].length) (baseStart_584396 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_584396 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_584396 prefixEnd_584396 := by exact prefixLift 584396
  have htrace : WordTrace (prefixWord ++ tailWord_584396) baseStart_584396 baseEnd_584396 := by
    simpa [prefixWord, tailWord_584396, baseEnd_584396] using wordTrace_append hprefix tailTrace_584396
  have hstable : (prefixWord ++ tailWord_584396).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584396).length < 2 ^ (prefixWord ++ tailWord_584396).sum := by decide
  have hdescent : baseEnd_584396 < baseStart_584396 := by decide
  rcases family_descends (prefixWord ++ tailWord_584396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584455 : List Nat := [1, 1, 4, 4, 1, 2, 1, 7]
def baseStart_584455 : Nat := 118140960795 + 584455 * 2 ^ 59
def prefixEnd_584455 : Nat := 4983230072969 + 3 ^ 40 * 584455 * 2
def baseEnd_584455 : Nat := 44460197914609785307355

theorem tailTrace_584455 : CollatzResearch.WordTrace tailWord_584455 prefixEnd_584455 44460197914609785307355 := by
  unfold tailWord_584455
  simp only [CollatzResearch.WordTrace]
  refine ⟨21316825097626826812274819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14211216731751217874849879 21316825097626826812274819)
  ·
    refine ⟨31975237646440240218412229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21316825097626826812274819 31975237646440240218412229)
    ·
      refine ⟨5995357058707545040952293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31975237646440240218412229 5995357058707545040952293)
      ·
        refine ⟨1124129448507664695178555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5995357058707545040952293 1124129448507664695178555)
        ·
          refine ⟨1686194172761497042767833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1124129448507664695178555 1686194172761497042767833)
          ·
            refine ⟨1264645629571122782075875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1686194172761497042767833 1264645629571122782075875)
            ·
              refine ⟨1896968444356684173113813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1264645629571122782075875 1896968444356684173113813)
              ·
                refine ⟨44460197914609785307355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1896968444356684173113813 44460197914609785307355)
                ·
                  rfl

theorem cell21_584455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 7].length) (baseStart_584455 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_584455 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_584455 prefixEnd_584455 := by exact prefixLift 584455
  have htrace : WordTrace (prefixWord ++ tailWord_584455) baseStart_584455 baseEnd_584455 := by
    simpa [prefixWord, tailWord_584455, baseEnd_584455] using wordTrace_append hprefix tailTrace_584455
  have hstable : (prefixWord ++ tailWord_584455).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584455).length < 2 ^ (prefixWord ++ tailWord_584455).sum := by decide
  have hdescent : baseEnd_584455 < baseStart_584455 := by decide
  rcases family_descends (prefixWord ++ tailWord_584455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584610 : List Nat := [3, 3, 1, 2, 2, 2, 3, 1, 4]
def baseStart_584610 : Nat := 118140960795 + 584610 * 2 ^ 59
def prefixEnd_584610 : Nat := 4983230072969 + 3 ^ 40 * 584610 * 2
def baseEnd_584610 : Nat := 133415966855583530838415

theorem tailTrace_584610 : CollatzResearch.WordTrace tailWord_584610 prefixEnd_584610 133415966855583530838415 := by
  unfold tailWord_584610
  simp only [CollatzResearch.WordTrace]
  refine ⟨5330619603016322071041821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14214985608043525522778189 5330619603016322071041821)
  ·
    refine ⟨1998982351131120776640683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5330619603016322071041821 1998982351131120776640683)
    ·
      refine ⟨2998473526696681164961025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1998982351131120776640683 2998473526696681164961025)
      ·
        refine ⟨2248855145022510873720769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2998473526696681164961025 2248855145022510873720769)
        ·
          refine ⟨1686641358766883155290577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2248855145022510873720769 1686641358766883155290577)
          ·
            refine ⟨1264981019075162366467933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1686641358766883155290577 1264981019075162366467933)
            ·
              refine ⟨474367882153185887425475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1264981019075162366467933 474367882153185887425475)
              ·
                refine ⟨711551823229778831138213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 474367882153185887425475 711551823229778831138213)
                ·
                  refine ⟨133415966855583530838415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 711551823229778831138213 133415966855583530838415)
                  ·
                    rfl

theorem cell21_584610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_584610 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_584610 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_584610 prefixEnd_584610 := by exact prefixLift 584610
  have htrace : WordTrace (prefixWord ++ tailWord_584610) baseStart_584610 baseEnd_584610 := by
    simpa [prefixWord, tailWord_584610, baseEnd_584610] using wordTrace_append hprefix tailTrace_584610
  have hstable : (prefixWord ++ tailWord_584610).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584610).length < 2 ^ (prefixWord ++ tailWord_584610).sum := by decide
  have hdescent : baseEnd_584610 < baseStart_584610 := by decide
  rcases family_descends (prefixWord ++ tailWord_584610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584652 : List Nat := [2, 2, 1, 4, 1, 1, 2, 4, 4]
def baseStart_584652 : Nat := 118140960795 + 584652 * 2 ^ 59
def prefixEnd_584652 : Nat := 4983230072969 + 3 ^ 40 * 584652 * 2
def baseEnd_584652 : Nat := 133425551827800791138329

theorem tailTrace_584652 : CollatzResearch.WordTrace tailWord_584652 prefixEnd_584652 133425551827800791138329 := by
  unfold tailWord_584652
  simp only [CollatzResearch.WordTrace]
  refine ⟨10662005138956564728598105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14216006851942086304797473 10662005138956564728598105)
  ·
    refine ⟨7996503854217423546448579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10662005138956564728598105 7996503854217423546448579)
    ·
      refine ⟨11994755781326135319672869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7996503854217423546448579 11994755781326135319672869)
      ·
        refine ⟨2249016708998650372438663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11994755781326135319672869 2249016708998650372438663)
        ·
          refine ⟨3373525063497975558657995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2249016708998650372438663 3373525063497975558657995)
          ·
            refine ⟨5060287595246963337986993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3373525063497975558657995 5060287595246963337986993)
            ·
              refine ⟨3795215696435222503490245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5060287595246963337986993 3795215696435222503490245)
              ·
                refine ⟨711602943081604219404421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3795215696435222503490245 711602943081604219404421)
                ·
                  refine ⟨133425551827800791138329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 711602943081604219404421 133425551827800791138329)
                  ·
                    rfl

theorem cell21_584652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 4, 4].length) (baseStart_584652 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_584652 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_584652 prefixEnd_584652 := by exact prefixLift 584652
  have htrace : WordTrace (prefixWord ++ tailWord_584652) baseStart_584652 baseEnd_584652 := by
    simpa [prefixWord, tailWord_584652, baseEnd_584652] using wordTrace_append hprefix tailTrace_584652
  have hstable : (prefixWord ++ tailWord_584652).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584652).length < 2 ^ (prefixWord ++ tailWord_584652).sum := by decide
  have hdescent : baseEnd_584652 < baseStart_584652 := by decide
  rcases family_descends (prefixWord ++ tailWord_584652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584655 : List Nat := [1, 1, 2, 1, 1, 7, 3, 2, 3]
def baseStart_584655 : Nat := 118140960795 + 584655 * 2 ^ 59
def prefixEnd_584655 : Nat := 4983230072969 + 3 ^ 40 * 584655 * 2
def baseEnd_584655 : Nat := 133426236468673452588323

theorem tailTrace_584655 : CollatzResearch.WordTrace tailWord_584655 prefixEnd_584655 133426236468673452588323 := by
  unfold tailWord_584655
  simp only [CollatzResearch.WordTrace]
  refine ⟨21324119696902260969555419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14216079797934840646370279 21324119696902260969555419)
  ·
    refine ⟨31986179545353391454333129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21324119696902260969555419 31986179545353391454333129)
    ·
      refine ⟨23989634659015043590749847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31986179545353391454333129 23989634659015043590749847)
      ·
        refine ⟨35984451988522565386124771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23989634659015043590749847 35984451988522565386124771)
        ·
          refine ⟨53976677982783848079187157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35984451988522565386124771 53976677982783848079187157)
          ·
            refine ⟨1265078390221496439355949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 53976677982783848079187157 1265078390221496439355949)
            ·
              refine ⟨474404396333061164758481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1265078390221496439355949 474404396333061164758481)
              ·
                refine ⟨355803297249795873568861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 474404396333061164758481 355803297249795873568861)
                ·
                  refine ⟨133426236468673452588323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 355803297249795873568861 133426236468673452588323)
                  ·
                    rfl

theorem cell21_584655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 2, 3].length) (baseStart_584655 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_584655 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_584655 prefixEnd_584655 := by exact prefixLift 584655
  have htrace : WordTrace (prefixWord ++ tailWord_584655) baseStart_584655 baseEnd_584655 := by
    simpa [prefixWord, tailWord_584655, baseEnd_584655] using wordTrace_append hprefix tailTrace_584655
  have hstable : (prefixWord ++ tailWord_584655).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584655).length < 2 ^ (prefixWord ++ tailWord_584655).sum := by decide
  have hdescent : baseEnd_584655 < baseStart_584655 := by decide
  rcases family_descends (prefixWord ++ tailWord_584655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584666 : List Nat := [3, 1, 1, 2, 4, 1, 1, 8]
def baseStart_584666 : Nat := 118140960795 + 584666 * 2 ^ 59
def prefixEnd_584666 : Nat := 4983230072969 + 3 ^ 40 * 584666 * 2
def baseEnd_584666 : Nat := 44476248939513292634989

theorem tailTrace_584666 : CollatzResearch.WordTrace tailWord_584666 prefixEnd_584666 44476248939513292634989 := by
  unfold tailWord_584666
  simp only [CollatzResearch.WordTrace]
  refine ⟨5331130224965602462051463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14216347266574939898803901 5331130224965602462051463)
  ·
    refine ⟨7996695337448403693077195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5331130224965602462051463 7996695337448403693077195)
    ·
      refine ⟨11995043006172605539615793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7996695337448403693077195 11995043006172605539615793)
      ·
        refine ⟨8996282254629454154711845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11995043006172605539615793 8996282254629454154711845)
        ·
          refine ⟨1686802922743022654008471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8996282254629454154711845 1686802922743022654008471)
          ·
            refine ⟨2530204384114533981012707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1686802922743022654008471 2530204384114533981012707)
            ·
              refine ⟨3795306576171800971519061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2530204384114533981012707 3795306576171800971519061)
              ·
                refine ⟨44476248939513292634989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3795306576171800971519061 44476248939513292634989)
                ·
                  rfl

theorem cell21_584666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 8].length) (baseStart_584666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_584666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_584666 prefixEnd_584666 := by exact prefixLift 584666
  have htrace : WordTrace (prefixWord ++ tailWord_584666) baseStart_584666 baseEnd_584666 := by
    simpa [prefixWord, tailWord_584666, baseEnd_584666] using wordTrace_append hprefix tailTrace_584666
  have hstable : (prefixWord ++ tailWord_584666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584666).length < 2 ^ (prefixWord ++ tailWord_584666).sum := by decide
  have hdescent : baseEnd_584666 < baseStart_584666 := by decide
  rcases family_descends (prefixWord ++ tailWord_584666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584669 : List Nat := [1, 4, 3, 1, 2, 2, 1, 3, 4]
def baseStart_584669 : Nat := 118140960795 + 584669 * 2 ^ 59
def prefixEnd_584669 : Nat := 4983230072969 + 3 ^ 40 * 584669 * 2
def baseEnd_584669 : Nat := 133429431459412539354961

theorem tailTrace_584669 : CollatzResearch.WordTrace tailWord_584669 prefixEnd_584669 133429431459412539354961 := by
  unfold tailWord_584669
  simp only [CollatzResearch.WordTrace]
  refine ⟨21324630318851541360565061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14216420212567694240376707 21324630318851541360565061)
  ·
    refine ⟨3998368184784664005105949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21324630318851541360565061 3998368184784664005105949)
    ·
      refine ⟨1499388069294249001914731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3998368184784664005105949 1499388069294249001914731)
      ·
        refine ⟨2249082103941373502872097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1499388069294249001914731 2249082103941373502872097)
        ·
          refine ⟨1686811577956030127154073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2249082103941373502872097 1686811577956030127154073)
          ·
            refine ⟨1265108683467022595365555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1686811577956030127154073 1265108683467022595365555)
            ·
              refine ⟨1897663025200533893048333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1265108683467022595365555 1897663025200533893048333)
              ·
                refine ⟨711623634450200209893125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1897663025200533893048333 711623634450200209893125)
                ·
                  refine ⟨133429431459412539354961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 711623634450200209893125 133429431459412539354961)
                  ·
                    rfl

theorem cell21_584669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_584669 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_584669 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_584669 prefixEnd_584669 := by exact prefixLift 584669
  have htrace : WordTrace (prefixWord ++ tailWord_584669) baseStart_584669 baseEnd_584669 := by
    simpa [prefixWord, tailWord_584669, baseEnd_584669] using wordTrace_append hprefix tailTrace_584669
  have hstable : (prefixWord ++ tailWord_584669).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584669).length < 2 ^ (prefixWord ++ tailWord_584669).sum := by decide
  have hdescent : baseEnd_584669 < baseStart_584669 := by decide
  rcases family_descends (prefixWord ++ tailWord_584669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584706 : List Nat := [3, 4, 1, 3, 1, 2, 2, 2, 3]
def baseStart_584706 : Nat := 118140960795 + 584706 * 2 ^ 59
def prefixEnd_584706 : Nat := 4983230072969 + 3 ^ 40 * 584706 * 2
def baseEnd_584706 : Nat := 133437875363508697238219

theorem tailTrace_584706 : CollatzResearch.WordTrace tailWord_584706 prefixEnd_584706 133437875363508697238219 := by
  unfold tailWord_584706
  simp only [CollatzResearch.WordTrace]
  refine ⟨5331494954929374169915493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14217319879811664453107981 5331494954929374169915493)
  ·
    refine ⟨999655304049257656859155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5331494954929374169915493 999655304049257656859155)
    ·
      refine ⟨1499482956073886485288733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 999655304049257656859155 1499482956073886485288733)
      ·
        refine ⟨562306108527707431983275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1499482956073886485288733 562306108527707431983275)
        ·
          refine ⟨843459162791561147974913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 562306108527707431983275 843459162791561147974913)
          ·
            refine ⟨632594372093670860981185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 843459162791561147974913 632594372093670860981185)
            ·
              refine ⟨474445779070253145735889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 632594372093670860981185 474445779070253145735889)
              ·
                refine ⟨355834334302689859301917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 474445779070253145735889 355834334302689859301917)
                ·
                  refine ⟨133437875363508697238219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 355834334302689859301917 133437875363508697238219)
                  ·
                    rfl

theorem cell21_584706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_584706 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_584706 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_584706 prefixEnd_584706 := by exact prefixLift 584706
  have htrace : WordTrace (prefixWord ++ tailWord_584706) baseStart_584706 baseEnd_584706 := by
    simpa [prefixWord, tailWord_584706, baseEnd_584706] using wordTrace_append hprefix tailTrace_584706
  have hstable : (prefixWord ++ tailWord_584706).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584706).length < 2 ^ (prefixWord ++ tailWord_584706).sum := by decide
  have hdescent : baseEnd_584706 < baseStart_584706 := by decide
  rcases family_descends (prefixWord ++ tailWord_584706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584728 : List Nat := [2, 1, 2, 3, 2, 2, 2, 3, 4]
def baseStart_584728 : Nat := 118140960795 + 584728 * 2 ^ 59
def prefixEnd_584728 : Nat := 4983230072969 + 3 ^ 40 * 584728 * 2
def baseEnd_584728 : Nat := 133442896063241547871507

theorem tailTrace_584728 : CollatzResearch.WordTrace tailWord_584728 prefixEnd_584728 133442896063241547871507 := by
  unfold tailWord_584728
  simp only [CollatzResearch.WordTrace]
  refine ⟨10663391112818897218481419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14217854817091862957975225 10663391112818897218481419)
  ·
    refine ⟨15995086669228345827722129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10663391112818897218481419 15995086669228345827722129)
    ·
      refine ⟨11996315001921259370791597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15995086669228345827722129 11996315001921259370791597)
      ·
        refine ⟨4498618125720472264046849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11996315001921259370791597 4498618125720472264046849)
        ·
          refine ⟨3373963594290354198035137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4498618125720472264046849 3373963594290354198035137)
          ·
            refine ⟨2530472695717765648526353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3373963594290354198035137 2530472695717765648526353)
            ·
              refine ⟨1897854521788324236394765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2530472695717765648526353 1897854521788324236394765)
              ·
                refine ⟨711695445670621588648037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1897854521788324236394765 711695445670621588648037)
                ·
                  refine ⟨133442896063241547871507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 711695445670621588648037 133442896063241547871507)
                  ·
                    rfl

theorem cell21_584728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 3, 4].length) (baseStart_584728 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_584728 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_584728 prefixEnd_584728 := by exact prefixLift 584728
  have htrace : WordTrace (prefixWord ++ tailWord_584728) baseStart_584728 baseEnd_584728 := by
    simpa [prefixWord, tailWord_584728, baseEnd_584728] using wordTrace_append hprefix tailTrace_584728
  have hstable : (prefixWord ++ tailWord_584728).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584728).length < 2 ^ (prefixWord ++ tailWord_584728).sum := by decide
  have hdescent : baseEnd_584728 < baseStart_584728 := by decide
  rcases family_descends (prefixWord ++ tailWord_584728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584807 : List Nat := [1, 1, 5, 1, 1, 5, 1, 3, 3]
def baseStart_584807 : Nat := 118140960795 + 584807 * 2 ^ 59
def prefixEnd_584807 : Nat := 4983230072969 + 3 ^ 40 * 584807 * 2
def baseEnd_584807 : Nat := 133460924939554966054679

theorem tailTrace_584807 : CollatzResearch.WordTrace tailWord_584807 prefixEnd_584807 133460924939554966054679 := by
  unfold tailWord_584807
  simp only [CollatzResearch.WordTrace]
  refine ⟨21329663592351590929088675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14219775728234393952725783 21329663592351590929088675)
  ·
    refine ⟨31994495388527386393633013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21329663592351590929088675 31994495388527386393633013)
    ·
      refine ⟨2999483942674442474403095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31994495388527386393633013 2999483942674442474403095)
      ·
        refine ⟨4499225914011663711604643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2999483942674442474403095 4499225914011663711604643)
        ·
          refine ⟨6748838871017495567406965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4499225914011663711604643 6748838871017495567406965)
          ·
            refine ⟨632703644157890209444403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6748838871017495567406965 632703644157890209444403)
            ·
              refine ⟨949055466236835314166605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 632703644157890209444403 949055466236835314166605)
              ·
                refine ⟨355895799838813242812477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 949055466236835314166605 355895799838813242812477)
                ·
                  refine ⟨133460924939554966054679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 355895799838813242812477 133460924939554966054679)
                  ·
                    rfl

theorem cell21_584807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 3, 3].length) (baseStart_584807 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_584807 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_584807 prefixEnd_584807 := by exact prefixLift 584807
  have htrace : WordTrace (prefixWord ++ tailWord_584807) baseStart_584807 baseEnd_584807 := by
    simpa [prefixWord, tailWord_584807, baseEnd_584807] using wordTrace_append hprefix tailTrace_584807
  have hstable : (prefixWord ++ tailWord_584807).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584807).length < 2 ^ (prefixWord ++ tailWord_584807).sum := by decide
  have hdescent : baseEnd_584807 < baseStart_584807 := by decide
  rcases family_descends (prefixWord ++ tailWord_584807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584886 : List Nat := [5, 1, 3, 2, 2, 1, 1, 6]
def baseStart_584886 : Nat := 118140960795 + 584886 * 2 ^ 59
def prefixEnd_584886 : Nat := 4983230072969 + 3 ^ 40 * 584886 * 2
def baseEnd_584886 : Nat := 44492984605289461412617

theorem tailTrace_584886 : CollatzResearch.WordTrace tailWord_584886 prefixEnd_584886 44492984605289461412617 := by
  unfold tailWord_584886
  simp only [CollatzResearch.WordTrace]
  refine ⟨1333284059941586713825907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14221696639376924947476341 1333284059941586713825907)
  ·
    refine ⟨1999926089912380070738861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1333284059941586713825907 1999926089912380070738861)
    ·
      refine ⟨749972283717142526527073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1999926089912380070738861 749972283717142526527073)
      ·
        refine ⟨562479212787856894895305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 749972283717142526527073 562479212787856894895305)
        ·
          refine ⟨421859409590892671171479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 562479212787856894895305 421859409590892671171479)
          ·
            refine ⟨632789114386339006757219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 421859409590892671171479 632789114386339006757219)
            ·
              refine ⟨949183671579508510135829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 632789114386339006757219 949183671579508510135829)
              ·
                refine ⟨44492984605289461412617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 949183671579508510135829 44492984605289461412617)
                ·
                  rfl

theorem cell21_584886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_584886 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_584886 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_584886 prefixEnd_584886 := by exact prefixLift 584886
  have htrace : WordTrace (prefixWord ++ tailWord_584886) baseStart_584886 baseEnd_584886 := by
    simpa [prefixWord, tailWord_584886, baseEnd_584886] using wordTrace_append hprefix tailTrace_584886
  have hstable : (prefixWord ++ tailWord_584886).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584886).length < 2 ^ (prefixWord ++ tailWord_584886).sum := by decide
  have hdescent : baseEnd_584886 < baseStart_584886 := by decide
  rcases family_descends (prefixWord ++ tailWord_584886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584897 : List Nat := [1, 2, 6, 1, 1, 1, 2, 3, 4]
def baseStart_584897 : Nat := 118140960795 + 584897 * 2 ^ 59
def prefixEnd_584897 : Nat := 4983230072969 + 3 ^ 40 * 584897 * 2
def baseEnd_584897 : Nat := 133481464165734809554495

theorem tailTrace_584897 : CollatzResearch.WordTrace tailWord_584897 prefixEnd_584897 133481464165734809554495 := by
  unfold tailWord_584897
  simp only [CollatzResearch.WordTrace]
  refine ⟨21332946162025536299864945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14221964108017024199909963 21332946162025536299864945)
  ·
    refine ⟨15999709621519152224898709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21332946162025536299864945 15999709621519152224898709)
    ·
      refine ⟨749986388508710260542127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15999709621519152224898709 749986388508710260542127)
      ·
        refine ⟨1124979582763065390813191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 749986388508710260542127 1124979582763065390813191)
        ·
          refine ⟨1687469374144598086219787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1124979582763065390813191 1687469374144598086219787)
          ·
            refine ⟨2531204061216897129329681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1687469374144598086219787 2531204061216897129329681)
            ·
              refine ⟨1898403045912672846997261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2531204061216897129329681 1898403045912672846997261)
              ·
                refine ⟨711901142217252317623973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1898403045912672846997261 711901142217252317623973)
                ·
                  refine ⟨133481464165734809554495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 711901142217252317623973 133481464165734809554495)
                  ·
                    rfl

theorem cell21_584897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 3, 4].length) (baseStart_584897 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_584897 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_584897 prefixEnd_584897 := by exact prefixLift 584897
  have htrace : WordTrace (prefixWord ++ tailWord_584897) baseStart_584897 baseEnd_584897 := by
    simpa [prefixWord, tailWord_584897, baseEnd_584897] using wordTrace_append hprefix tailTrace_584897
  have hstable : (prefixWord ++ tailWord_584897).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584897).length < 2 ^ (prefixWord ++ tailWord_584897).sum := by decide
  have hdescent : baseEnd_584897 < baseStart_584897 := by decide
  rcases family_descends (prefixWord ++ tailWord_584897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584939 : List Nat := [1, 1, 1, 1, 2, 7, 1, 1, 6]
def baseStart_584939 : Nat := 118140960795 + 584939 * 2 ^ 59
def prefixEnd_584939 : Nat := 4983230072969 + 3 ^ 40 * 584939 * 2
def baseEnd_584939 : Nat := 133491049137952069854409

theorem tailTrace_584939 : CollatzResearch.WordTrace tailWord_584939 prefixEnd_584939 133491049137952069854409 := by
  unfold tailWord_584939
  simp only [CollatzResearch.WordTrace]
  refine ⟨21334478027873377472893871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14222985351915584981929247 21334478027873377472893871)
  ·
    refine ⟨32001717041810066209340807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21334478027873377472893871 32001717041810066209340807)
    ·
      refine ⟨48002575562715099314011211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32001717041810066209340807 48002575562715099314011211)
      ·
        refine ⟨72003863344072648971016817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48002575562715099314011211 72003863344072648971016817)
        ·
          refine ⟨54002897508054486728262613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72003863344072648971016817 54002897508054486728262613)
          ·
            refine ⟨1265692910345027032693655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 54002897508054486728262613 1265692910345027032693655)
            ·
              refine ⟨1898539365517540549040483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1265692910345027032693655 1898539365517540549040483)
              ·
                refine ⟨2847809048276310823560725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1898539365517540549040483 2847809048276310823560725)
                ·
                  refine ⟨133491049137952069854409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2847809048276310823560725 133491049137952069854409)
                  ·
                    rfl

theorem cell21_584939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 6].length) (baseStart_584939 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_584939 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_584939 prefixEnd_584939 := by exact prefixLift 584939
  have htrace : WordTrace (prefixWord ++ tailWord_584939) baseStart_584939 baseEnd_584939 := by
    simpa [prefixWord, tailWord_584939, baseEnd_584939] using wordTrace_append hprefix tailTrace_584939
  have hstable : (prefixWord ++ tailWord_584939).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584939).length < 2 ^ (prefixWord ++ tailWord_584939).sum := by decide
  have hdescent : baseEnd_584939 < baseStart_584939 := by decide
  rcases family_descends (prefixWord ++ tailWord_584939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584942 : List Nat := [4, 1, 2, 1, 1, 1, 4, 4, 3]
def baseStart_584942 : Nat := 118140960795 + 584942 * 2 ^ 59
def prefixEnd_584942 : Nat := 4983230072969 + 3 ^ 40 * 584942 * 2
def baseEnd_584942 : Nat := 133491733778824731304403

theorem tailTrace_584942 : CollatzResearch.WordTrace tailWord_584942 prefixEnd_584942 133491733778824731304403 := by
  unfold tailWord_584942
  simp only [CollatzResearch.WordTrace]
  refine ⟨2666823430857813623156635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14223058297908339323502053 2666823430857813623156635)
  ·
    refine ⟨4000235146286720434734953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2666823430857813623156635 4000235146286720434734953)
    ·
      refine ⟨3000176359715040326051215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4000235146286720434734953 3000176359715040326051215)
      ·
        refine ⟨4500264539572560489076823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3000176359715040326051215 4500264539572560489076823)
        ·
          refine ⟨6750396809358840733615235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4500264539572560489076823 6750396809358840733615235)
          ·
            refine ⟨10125595214038261100422853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6750396809358840733615235 10125595214038261100422853)
            ·
              refine ⟨1898549102632173956329285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10125595214038261100422853 1898549102632173956329285)
              ·
                refine ⟨355977956743532616811741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1898549102632173956329285 355977956743532616811741)
                ·
                  refine ⟨133491733778824731304403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 355977956743532616811741 133491733778824731304403)
                  ·
                    rfl

theorem cell21_584942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 4, 3].length) (baseStart_584942 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_584942 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_584942 prefixEnd_584942 := by exact prefixLift 584942
  have htrace : WordTrace (prefixWord ++ tailWord_584942) baseStart_584942 baseEnd_584942 := by
    simpa [prefixWord, tailWord_584942, baseEnd_584942] using wordTrace_append hprefix tailTrace_584942
  have hstable : (prefixWord ++ tailWord_584942).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584942).length < 2 ^ (prefixWord ++ tailWord_584942).sum := by decide
  have hdescent : baseEnd_584942 < baseStart_584942 := by decide
  rcases family_descends (prefixWord ++ tailWord_584942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584948 : List Nat := [2, 6, 1, 2, 1, 1, 3, 1, 4]
def baseStart_584948 : Nat := 118140960795 + 584948 * 2 ^ 59
def prefixEnd_584948 : Nat := 4983230072969 + 3 ^ 40 * 584948 * 2
def baseEnd_584948 : Nat := 133493103060570054204391

theorem tailTrace_584948 : CollatzResearch.WordTrace tailWord_584948 prefixEnd_584948 133493103060570054204391 := by
  unfold tailWord_584948
  simp only [CollatzResearch.WordTrace]
  refine ⟨10667403142420386004985749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14223204189893848006647665 10667403142420386004985749)
  ·
    refine ⟨500034522300955593983707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10667403142420386004985749 500034522300955593983707)
    ·
      refine ⟨750051783451433390975561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 500034522300955593983707 750051783451433390975561)
      ·
        refine ⟨562538837588575043231671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 750051783451433390975561 562538837588575043231671)
        ·
          refine ⟨843808256382862564847507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 562538837588575043231671 843808256382862564847507)
          ·
            refine ⟨1265712384574293847271261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 843808256382862564847507 1265712384574293847271261)
            ·
              refine ⟨474642144215360192726723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1265712384574293847271261 474642144215360192726723)
              ·
                refine ⟨711963216323040289090085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 474642144215360192726723 711963216323040289090085)
                ·
                  refine ⟨133493103060570054204391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 711963216323040289090085 133493103060570054204391)
                  ·
                    rfl

theorem cell21_584948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_584948 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_584948 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_584948 prefixEnd_584948 := by exact prefixLift 584948
  have htrace : WordTrace (prefixWord ++ tailWord_584948) baseStart_584948 baseEnd_584948 := by
    simpa [prefixWord, tailWord_584948, baseEnd_584948] using wordTrace_append hprefix tailTrace_584948
  have hstable : (prefixWord ++ tailWord_584948).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584948).length < 2 ^ (prefixWord ++ tailWord_584948).sum := by decide
  have hdescent : baseEnd_584948 < baseStart_584948 := by decide
  rcases family_descends (prefixWord ++ tailWord_584948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584953 : List Nat := [1, 2, 1, 3, 1, 1, 4, 8]
def baseStart_584953 : Nat := 118140960795 + 584953 * 2 ^ 59
def prefixEnd_584953 : Nat := 4983230072969 + 3 ^ 40 * 584953 * 2
def baseEnd_584953 : Nat := 44498081376230385540349

theorem tailTrace_584953 : CollatzResearch.WordTrace tailWord_584953 prefixEnd_584953 44498081376230385540349 := by
  unfold tailWord_584953
  simp only [CollatzResearch.WordTrace]
  refine ⟨21334988649822657863903513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14223325766548438575935675 21334988649822657863903513)
  ·
    refine ⟨16001241487366993397927635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21334988649822657863903513 16001241487366993397927635)
    ·
      refine ⟨24001862231050490096891453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16001241487366993397927635 24001862231050490096891453)
      ·
        refine ⟨9000698336643933786334295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24001862231050490096891453 9000698336643933786334295)
        ·
          refine ⟨13501047504965900679501443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9000698336643933786334295 13501047504965900679501443)
          ·
            refine ⟨20251571257448851019252165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13501047504965900679501443 20251571257448851019252165)
            ·
              refine ⟨3797169610771659566109781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20251571257448851019252165 3797169610771659566109781)
              ·
                refine ⟨44498081376230385540349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3797169610771659566109781 44498081376230385540349)
                ·
                  rfl

theorem cell21_584953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 8].length) (baseStart_584953 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_584953 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_584953 prefixEnd_584953 := by exact prefixLift 584953
  have htrace : WordTrace (prefixWord ++ tailWord_584953) baseStart_584953 baseEnd_584953 := by
    simpa [prefixWord, tailWord_584953, baseEnd_584953] using wordTrace_append hprefix tailTrace_584953
  have hstable : (prefixWord ++ tailWord_584953).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584953).length < 2 ^ (prefixWord ++ tailWord_584953).sum := by decide
  have hdescent : baseEnd_584953 < baseStart_584953 := by decide
  rcases family_descends (prefixWord ++ tailWord_584953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585063 : List Nat := [1, 1, 5, 1, 4, 2, 1, 6]
def baseStart_585063 : Nat := 118140960795 + 585063 * 2 ^ 59
def prefixEnd_585063 : Nat := 4983230072969 + 3 ^ 40 * 585063 * 2
def baseEnd_585063 : Nat := 44506449209118469929163

theorem tailTrace_585063 : CollatzResearch.WordTrace tailWord_585063 prefixEnd_585063 44506449209118469929163 := by
  unfold tailWord_585063
  simp only [CollatzResearch.WordTrace]
  refine ⟨21339000679424146650407843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14226000452949431100271895 21339000679424146650407843)
  ·
    refine ⟨32008501019136219975611765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21339000679424146650407843 32008501019136219975611765)
    ·
      refine ⟨3000796970544020622713603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32008501019136219975611765 3000796970544020622713603)
      ·
        refine ⟨4501195455816030934070405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3000796970544020622713603 4501195455816030934070405)
        ·
          refine ⟨843974147965505800138201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4501195455816030934070405 843974147965505800138201)
          ·
            refine ⟨632980610974129350103651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 843974147965505800138201 632980610974129350103651)
            ·
              refine ⟨949470916461194025155477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 632980610974129350103651 949470916461194025155477)
              ·
                refine ⟨44506449209118469929163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 949470916461194025155477 44506449209118469929163)
                ·
                  rfl

theorem cell21_585063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 6].length) (baseStart_585063 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_585063 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_585063 prefixEnd_585063 := by exact prefixLift 585063
  have htrace : WordTrace (prefixWord ++ tailWord_585063) baseStart_585063 baseEnd_585063 := by
    simpa [prefixWord, tailWord_585063, baseEnd_585063] using wordTrace_append hprefix tailTrace_585063
  have hstable : (prefixWord ++ tailWord_585063).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585063).length < 2 ^ (prefixWord ++ tailWord_585063).sum := by decide
  have hdescent : baseEnd_585063 < baseStart_585063 := by decide
  rcases family_descends (prefixWord ++ tailWord_585063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585108 : List Nat := [2, 4, 2, 1, 2, 2, 1, 1, 6]
def baseStart_585108 : Nat := 118140960795 + 585108 * 2 ^ 59
def prefixEnd_585108 : Nat := 4983230072969 + 3 ^ 40 * 585108 * 2
def baseEnd_585108 : Nat := 133529617240445331537397

theorem tailTrace_585108 : CollatzResearch.WordTrace tailWord_585108 prefixEnd_585108 133529617240445331537397 := by
  unfold tailWord_585108
  simp only [CollatzResearch.WordTrace]
  refine ⟨10670320982130559667897989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14227094642840746223863985 10670320982130559667897989)
  ·
    refine ⟨2000685184149479937730873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10670320982130559667897989 2000685184149479937730873)
    ·
      refine ⟨1500513888112109953298155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2000685184149479937730873 1500513888112109953298155)
      ·
        refine ⟨2250770832168164929947233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1500513888112109953298155 2250770832168164929947233)
        ·
          refine ⟨1688078124126123697460425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2250770832168164929947233 1688078124126123697460425)
          ·
            refine ⟨1266058593094592773095319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1688078124126123697460425 1266058593094592773095319)
            ·
              refine ⟨1899087889641889159642979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1266058593094592773095319 1899087889641889159642979)
              ·
                refine ⟨2848631834462833739464469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1899087889641889159642979 2848631834462833739464469)
                ·
                  refine ⟨133529617240445331537397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2848631834462833739464469 133529617240445331537397)
                  ·
                    rfl

theorem cell21_585108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_585108 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_585108 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_585108 prefixEnd_585108 := by exact prefixLift 585108
  have htrace : WordTrace (prefixWord ++ tailWord_585108) baseStart_585108 baseEnd_585108 := by
    simpa [prefixWord, tailWord_585108, baseEnd_585108] using wordTrace_append hprefix tailTrace_585108
  have hstable : (prefixWord ++ tailWord_585108).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585108).length < 2 ^ (prefixWord ++ tailWord_585108).sum := by decide
  have hdescent : baseEnd_585108 < baseStart_585108 := by decide
  rcases family_descends (prefixWord ++ tailWord_585108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585277 : List Nat := [1, 4, 1, 3, 3, 2, 1, 2, 4]
def baseStart_585277 : Nat := 118140960795 + 585277 * 2 ^ 59
def prefixEnd_585277 : Nat := 4983230072969 + 3 ^ 40 * 585277 * 2
def baseEnd_585277 : Nat := 133568185342938593220385

theorem tailTrace_585277 : CollatzResearch.WordTrace tailWord_585277 prefixEnd_585277 133568185342938593220385 := by
  unfold tailWord_585277
  simp only [CollatzResearch.WordTrace]
  refine ⟨21346805900648861198698085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14231203933765907465798723 21346805900648861198698085)
  ·
    refine ⟨4002526106371661474755891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21346805900648861198698085 4002526106371661474755891)
    ·
      refine ⟨6003789159557492212133837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4002526106371661474755891 6003789159557492212133837)
      ·
        refine ⟨2251420934834059579550189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6003789159557492212133837 2251420934834059579550189)
        ·
          refine ⟨844282850562772342331321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2251420934834059579550189 844282850562772342331321)
          ·
            refine ⟨633212137922079256748491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 844282850562772342331321 633212137922079256748491)
            ·
              refine ⟨949818206883118885122737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 633212137922079256748491 949818206883118885122737)
              ·
                refine ⟨712363655162339163842053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 949818206883118885122737 712363655162339163842053)
                ·
                  refine ⟨133568185342938593220385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 712363655162339163842053 133568185342938593220385)
                  ·
                    rfl

theorem cell21_585277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 2, 4].length) (baseStart_585277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_585277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_585277 prefixEnd_585277 := by exact prefixLift 585277
  have htrace : WordTrace (prefixWord ++ tailWord_585277) baseStart_585277 baseEnd_585277 := by
    simpa [prefixWord, tailWord_585277, baseEnd_585277] using wordTrace_append hprefix tailTrace_585277
  have hstable : (prefixWord ++ tailWord_585277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585277).length < 2 ^ (prefixWord ++ tailWord_585277).sum := by decide
  have hdescent : baseEnd_585277 < baseStart_585277 := by decide
  rcases family_descends (prefixWord ++ tailWord_585277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585322 : List Nat := [3, 1, 3, 2, 1, 2, 3, 3, 3]
def baseStart_585322 : Nat := 118140960795 + 585322 * 2 ^ 59
def prefixEnd_585322 : Nat := 4983230072969 + 3 ^ 40 * 585322 * 2
def baseEnd_585322 : Nat := 133578454956028514970293

theorem tailTrace_585322 : CollatzResearch.WordTrace tailWord_585322 prefixEnd_585322 133578454956028514970293 := by
  unfold tailWord_585322
  simp only [CollatzResearch.WordTrace]
  refine ⟨5337111796371458471021555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14232298123657222589390813 5337111796371458471021555)
  ·
    refine ⟨8005667694557187706532333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5337111796371458471021555 8005667694557187706532333)
    ·
      refine ⟨3002125385458945389949625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8005667694557187706532333 3002125385458945389949625)
      ·
        refine ⟨2251594039094209042462219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3002125385458945389949625 2251594039094209042462219)
        ·
          refine ⟨3377391058641313563693329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2251594039094209042462219 3377391058641313563693329)
          ·
            refine ⟨2533043293980985172769997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3377391058641313563693329 2533043293980985172769997)
            ·
              refine ⟨949891235242869439788749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2533043293980985172769997 949891235242869439788749)
              ·
                refine ⟨356209213216076039920781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 949891235242869439788749 356209213216076039920781)
                ·
                  refine ⟨133578454956028514970293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 356209213216076039920781 133578454956028514970293)
                  ·
                    rfl

theorem cell21_585322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 3, 3].length) (baseStart_585322 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_585322 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_585322 prefixEnd_585322 := by exact prefixLift 585322
  have htrace : WordTrace (prefixWord ++ tailWord_585322) baseStart_585322 baseEnd_585322 := by
    simpa [prefixWord, tailWord_585322, baseEnd_585322] using wordTrace_append hprefix tailTrace_585322
  have hstable : (prefixWord ++ tailWord_585322).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585322).length < 2 ^ (prefixWord ++ tailWord_585322).sum := by decide
  have hdescent : baseEnd_585322 < baseStart_585322 := by decide
  rcases family_descends (prefixWord ++ tailWord_585322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585384 : List Nat := [2, 1, 7, 1, 2, 8]
def baseStart_585384 : Nat := 118140960795 + 585384 * 2 ^ 59
def prefixEnd_585384 : Nat := 4983230072969 + 3 ^ 40 * 585384 * 2
def baseEnd_585384 : Nat := 4947874229656673516179

theorem tailTrace_585384 : CollatzResearch.WordTrace tailWord_585384 prefixEnd_585384 4947874229656673516179 := by
  unfold tailWord_585384
  simp only [CollatzResearch.WordTrace]
  refine ⟨10675354255630609236421603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14233805674174145648562137 10675354255630609236421603)
  ·
    refine ⟨16013031383445913854632405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10675354255630609236421603 16013031383445913854632405)
    ·
      refine ⟨375305423049513605967947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 16013031383445913854632405 375305423049513605967947)
      ·
        refine ⟨562958134574270408951921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 375305423049513605967947 562958134574270408951921)
        ·
          refine ⟨422218600930702806713941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 562958134574270408951921 422218600930702806713941)
          ·
            refine ⟨4947874229656673516179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 422218600930702806713941 4947874229656673516179)
            ·
              rfl

theorem cell21_585384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 8].length) (baseStart_585384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_585384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_585384 prefixEnd_585384 := by exact prefixLift 585384
  have htrace : WordTrace (prefixWord ++ tailWord_585384) baseStart_585384 baseEnd_585384 := by
    simpa [prefixWord, tailWord_585384, baseEnd_585384] using wordTrace_append hprefix tailTrace_585384
  have hstable : (prefixWord ++ tailWord_585384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585384).length < 2 ^ (prefixWord ++ tailWord_585384).sum := by decide
  have hdescent : baseEnd_585384 < baseStart_585384 := by decide
  rcases family_descends (prefixWord ++ tailWord_585384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585395 : List Nat := [1, 1, 1, 2, 3, 3, 4, 2, 4]
def baseStart_585395 : Nat := 118140960795 + 585395 * 2 ^ 59
def prefixEnd_585395 : Nat := 4983230072969 + 3 ^ 40 * 585395 * 2
def baseEnd_585395 : Nat := 133595114550596610253477

theorem tailTrace_585395 : CollatzResearch.WordTrace tailWord_585395 prefixEnd_585395 133595114550596610253477 := by
  unfold tailWord_585395
  simp only [CollatzResearch.WordTrace]
  refine ⟨21351109714221367351493639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14234073142814244900995759 21351109714221367351493639)
  ·
    refine ⟨32026664571332051027240459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21351109714221367351493639 32026664571332051027240459)
    ·
      refine ⟨48039996856998076540860689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32026664571332051027240459 48039996856998076540860689)
      ·
        refine ⟨36029997642748557405645517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48039996856998076540860689 36029997642748557405645517)
        ·
          refine ⟨13511249116030709027117069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36029997642748557405645517 13511249116030709027117069)
          ·
            refine ⟨5066718418511515885168901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13511249116030709027117069 5066718418511515885168901)
            ·
              refine ⟨950009703470909228469169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5066718418511515885168901 950009703470909228469169)
              ·
                refine ⟨712507277603181921351877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 950009703470909228469169 712507277603181921351877)
                ·
                  refine ⟨133595114550596610253477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 712507277603181921351877 133595114550596610253477)
                  ·
                    rfl

theorem cell21_585395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 2, 4].length) (baseStart_585395 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_585395 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_585395 prefixEnd_585395 := by exact prefixLift 585395
  have htrace : WordTrace (prefixWord ++ tailWord_585395) baseStart_585395 baseEnd_585395 := by
    simpa [prefixWord, tailWord_585395, baseEnd_585395] using wordTrace_append hprefix tailTrace_585395
  have hstable : (prefixWord ++ tailWord_585395).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585395).length < 2 ^ (prefixWord ++ tailWord_585395).sum := by decide
  have hdescent : baseEnd_585395 < baseStart_585395 := by decide
  rcases family_descends (prefixWord ++ tailWord_585395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585457 : List Nat := [1, 2, 2, 2, 2, 3, 2, 4, 3]
def baseStart_585457 : Nat := 118140960795 + 585457 * 2 ^ 59
def prefixEnd_585457 : Nat := 4983230072969 + 3 ^ 40 * 585457 * 2
def baseEnd_585457 : Nat := 133609263795298280220017

theorem tailTrace_585457 : CollatzResearch.WordTrace tailWord_585457 prefixEnd_585457 133609263795298280220017 := by
  unfold tailWord_585457
  simp only [CollatzResearch.WordTrace]
  refine ⟨21353371039996751940250625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14235580693331167960167083 21353371039996751940250625)
  ·
    refine ⟨16015028279997563955187969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21353371039996751940250625 16015028279997563955187969)
    ·
      refine ⟨12011271209998172966390977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16015028279997563955187969 12011271209998172966390977)
      ·
        refine ⟨9008453407498629724793233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12011271209998172966390977 9008453407498629724793233)
        ·
          refine ⟨6756340055623972293594925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9008453407498629724793233 6756340055623972293594925)
          ·
            refine ⟨2533627520858989610098097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6756340055623972293594925 2533627520858989610098097)
            ·
              refine ⟨1900220640644242207573573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2533627520858989610098097 1900220640644242207573573)
              ·
                refine ⟨356291370120795413920045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1900220640644242207573573 356291370120795413920045)
                ·
                  refine ⟨133609263795298280220017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 356291370120795413920045 133609263795298280220017)
                  ·
                    rfl

theorem cell21_585457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 4, 3].length) (baseStart_585457 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_585457 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_585457 prefixEnd_585457 := by exact prefixLift 585457
  have htrace : WordTrace (prefixWord ++ tailWord_585457) baseStart_585457 baseEnd_585457 := by
    simpa [prefixWord, tailWord_585457, baseEnd_585457] using wordTrace_append hprefix tailTrace_585457
  have hstable : (prefixWord ++ tailWord_585457).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585457).length < 2 ^ (prefixWord ++ tailWord_585457).sum := by decide
  have hdescent : baseEnd_585457 < baseStart_585457 := by decide
  rcases family_descends (prefixWord ++ tailWord_585457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585516 : List Nat := [2, 2, 1, 1, 1, 5, 3, 1, 5]
def baseStart_585516 : Nat := 118140960795 + 585516 * 2 ^ 59
def prefixEnd_585516 : Nat := 4983230072969 + 3 ^ 40 * 585516 * 2
def baseEnd_585516 : Nat := 133622728399127288736563

theorem tailTrace_585516 : CollatzResearch.WordTrace tailWord_585516 prefixEnd_585516 133622728399127288736563 := by
  unfold tailWord_585516
  simp only [CollatzResearch.WordTrace]
  refine ⟨10677761473391502508324201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14237015297855336677765601 10677761473391502508324201)
  ·
    refine ⟨8008321105043626881243151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10677761473391502508324201 8008321105043626881243151)
    ·
      refine ⟨12012481657565440321864727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8008321105043626881243151 12012481657565440321864727)
      ·
        refine ⟨18018722486348160482797091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12012481657565440321864727 18018722486348160482797091)
        ·
          refine ⟨27028083729522240724195637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18018722486348160482797091 27028083729522240724195637)
          ·
            refine ⟨2533882849642710067893341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27028083729522240724195637 2533882849642710067893341)
            ·
              refine ⟨950206068616016275460003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2533882849642710067893341 950206068616016275460003)
              ·
                refine ⟨1425309102924024413190005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 950206068616016275460003 1425309102924024413190005)
                ·
                  refine ⟨133622728399127288736563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1425309102924024413190005 133622728399127288736563)
                  ·
                    rfl

theorem cell21_585516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 5].length) (baseStart_585516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_585516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_585516 prefixEnd_585516 := by exact prefixLift 585516
  have htrace : WordTrace (prefixWord ++ tailWord_585516) baseStart_585516 baseEnd_585516 := by
    simpa [prefixWord, tailWord_585516, baseEnd_585516] using wordTrace_append hprefix tailTrace_585516
  have hstable : (prefixWord ++ tailWord_585516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585516).length < 2 ^ (prefixWord ++ tailWord_585516).sum := by decide
  have hdescent : baseEnd_585516 < baseStart_585516 := by decide
  rcases family_descends (prefixWord ++ tailWord_585516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585609 : List Nat := [1, 2, 1, 1, 5, 1, 4, 3, 3]
def baseStart_585609 : Nat := 118140960795 + 585609 * 2 ^ 59
def prefixEnd_585609 : Nat := 4983230072969 + 3 ^ 40 * 585609 * 2
def baseEnd_585609 : Nat := 133643952266179793686373

theorem tailTrace_585609 : CollatzResearch.WordTrace tailWord_585609 prefixEnd_585609 133643952266179793686373 := by
  unfold tailWord_585609
  simp only [CollatzResearch.WordTrace]
  refine ⟨21358914935446081899783881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14239276623630721266522587 21358914935446081899783881)
  ·
    refine ⟨16019186201584561424837911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21358914935446081899783881 16019186201584561424837911)
    ·
      refine ⟨24028779302376842137256867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16019186201584561424837911 24028779302376842137256867)
      ·
        refine ⟨36043168953565263205885301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24028779302376842137256867 36043168953565263205885301)
        ·
          refine ⟨3379047089396743425551747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36043168953565263205885301 3379047089396743425551747)
          ·
            refine ⟨5068570634095115138327621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3379047089396743425551747 5068570634095115138327621)
            ·
              refine ⟨950356993892834088436429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5068570634095115138327621 950356993892834088436429)
              ·
                refine ⟨356383872709812783163661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 950356993892834088436429 356383872709812783163661)
                ·
                  refine ⟨133643952266179793686373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 356383872709812783163661 133643952266179793686373)
                  ·
                    rfl

theorem cell21_585609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 3, 3].length) (baseStart_585609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_585609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_585609 prefixEnd_585609 := by exact prefixLift 585609
  have htrace : WordTrace (prefixWord ++ tailWord_585609) baseStart_585609 baseEnd_585609 := by
    simpa [prefixWord, tailWord_585609, baseEnd_585609] using wordTrace_append hprefix tailTrace_585609
  have hstable : (prefixWord ++ tailWord_585609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585609).length < 2 ^ (prefixWord ++ tailWord_585609).sum := by decide
  have hdescent : baseEnd_585609 < baseStart_585609 := by decide
  rcases family_descends (prefixWord ++ tailWord_585609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585623 : List Nat := [1, 1, 3, 3, 1, 3, 3, 2, 4]
def baseStart_585623 : Nat := 118140960795 + 585623 * 2 ^ 59
def prefixEnd_585623 : Nat := 4983230072969 + 3 ^ 40 * 585623 * 2
def baseEnd_585623 : Nat := 133647147256918880453011

theorem tailTrace_585623 : CollatzResearch.WordTrace tailWord_585623 prefixEnd_585623 133647147256918880453011 := by
  unfold tailWord_585623
  simp only [CollatzResearch.WordTrace]
  refine ⟨21359425557395362290793523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14239617038263574860529015 21359425557395362290793523)
  ·
    refine ⟨32039138336093043436190285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21359425557395362290793523 32039138336093043436190285)
    ·
      refine ⟨12014676876034891288571357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32039138336093043436190285 12014676876034891288571357)
      ·
        refine ⟨4505503828513084233214259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12014676876034891288571357 4505503828513084233214259)
        ·
          refine ⟨6758255742769626349821389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4505503828513084233214259 6758255742769626349821389)
          ·
            refine ⟨2534345903538609881183021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6758255742769626349821389 2534345903538609881183021)
            ·
              refine ⟨950379713826978705443633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2534345903538609881183021 950379713826978705443633)
              ·
                refine ⟨712784785370234029082725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 950379713826978705443633 712784785370234029082725)
                ·
                  refine ⟨133647147256918880453011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 712784785370234029082725 133647147256918880453011)
                  ·
                    rfl

theorem cell21_585623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 2, 4].length) (baseStart_585623 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_585623 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_585623 prefixEnd_585623 := by exact prefixLift 585623
  have htrace : WordTrace (prefixWord ++ tailWord_585623) baseStart_585623 baseEnd_585623 := by
    simpa [prefixWord, tailWord_585623, baseEnd_585623] using wordTrace_append hprefix tailTrace_585623
  have hstable : (prefixWord ++ tailWord_585623).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585623).length < 2 ^ (prefixWord ++ tailWord_585623).sum := by decide
  have hdescent : baseEnd_585623 < baseStart_585623 := by decide
  rcases family_descends (prefixWord ++ tailWord_585623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585646 : List Nat := [4, 1, 5, 1, 2, 1, 2, 5]
def baseStart_585646 : Nat := 118140960795 + 585646 * 2 ^ 59
def prefixEnd_585646 : Nat := 4983230072969 + 3 ^ 40 * 585646 * 2
def baseEnd_585646 : Nat := 44550798723425317189877

theorem tailTrace_585646 : CollatzResearch.WordTrace tailWord_585646 prefixEnd_585646 44550798723425317189877 := by
  unfold tailWord_585646
  simp only [CollatzResearch.WordTrace]
  refine ⟨2670033054539004652360099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14240176290874691479253861 2670033054539004652360099)
  ·
    refine ⟨4005049581808506978540149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2670033054539004652360099 4005049581808506978540149)
    ·
      refine ⟨375473398294547529238139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4005049581808506978540149 375473398294547529238139)
      ·
        refine ⟨563210097441821293857209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 375473398294547529238139 563210097441821293857209)
        ·
          refine ⟨422407573081365970392907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 563210097441821293857209 422407573081365970392907)
          ·
            refine ⟨633611359622048955589361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 422407573081365970392907 633611359622048955589361)
            ·
              refine ⟨475208519716536716692021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 633611359622048955589361 475208519716536716692021)
              ·
                refine ⟨44550798723425317189877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 475208519716536716692021 44550798723425317189877)
                ·
                  rfl

theorem cell21_585646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 5].length) (baseStart_585646 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_585646 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_585646 prefixEnd_585646 := by exact prefixLift 585646
  have htrace : WordTrace (prefixWord ++ tailWord_585646) baseStart_585646 baseEnd_585646 := by
    simpa [prefixWord, tailWord_585646, baseEnd_585646] using wordTrace_append hprefix tailTrace_585646
  have hstable : (prefixWord ++ tailWord_585646).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585646).length < 2 ^ (prefixWord ++ tailWord_585646).sum := by decide
  have hdescent : baseEnd_585646 < baseStart_585646 := by decide
  rcases family_descends (prefixWord ++ tailWord_585646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585651 : List Nat := [1, 1, 1, 2, 3, 1, 3, 4, 5]
def baseStart_585651 : Nat := 118140960795 + 585651 * 2 ^ 59
def prefixEnd_585651 : Nat := 4983230072969 + 3 ^ 40 * 585651 * 2
def baseEnd_585651 : Nat := 133653537238397053986287

theorem tailTrace_585651 : CollatzResearch.WordTrace tailWord_585651 prefixEnd_585651 133653537238397053986287 := by
  unfold tailWord_585651
  simp only [CollatzResearch.WordTrace]
  refine ⟨21360446801293923072812807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14240297867529282048541871 21360446801293923072812807)
  ·
    refine ⟨32040670201940884609219211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21360446801293923072812807 32040670201940884609219211)
    ·
      refine ⟨48061005302911326913828817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32040670201940884609219211 48061005302911326913828817)
      ·
        refine ⟨36045753977183495185371613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48061005302911326913828817 36045753977183495185371613)
        ·
          refine ⟨13517157741443810694514355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36045753977183495185371613 13517157741443810694514355)
          ·
            refine ⟨20275736612165716041771533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13517157741443810694514355 20275736612165716041771533)
            ·
              refine ⟨7603401229562143515664325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20275736612165716041771533 7603401229562143515664325)
              ·
                refine ⟨1425637730542901909187061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7603401229562143515664325 1425637730542901909187061)
                ·
                  refine ⟨133653537238397053986287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1425637730542901909187061 133653537238397053986287)
                  ·
                    rfl

theorem cell21_585651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4, 5].length) (baseStart_585651 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_585651 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_585651 prefixEnd_585651 := by exact prefixLift 585651
  have htrace : WordTrace (prefixWord ++ tailWord_585651) baseStart_585651 baseEnd_585651 := by
    simpa [prefixWord, tailWord_585651, baseEnd_585651] using wordTrace_append hprefix tailTrace_585651
  have hstable : (prefixWord ++ tailWord_585651).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585651).length < 2 ^ (prefixWord ++ tailWord_585651).sum := by decide
  have hdescent : baseEnd_585651 < baseStart_585651 := by decide
  rcases family_descends (prefixWord ++ tailWord_585651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585660 : List Nat := [2, 2, 2, 5, 2, 1, 1, 3, 3]
def baseStart_585660 : Nat := 118140960795 + 585660 * 2 ^ 59
def prefixEnd_585660 : Nat := 4983230072969 + 3 ^ 40 * 585660 * 2
def baseEnd_585660 : Nat := 133655591161015038336269

theorem tailTrace_585660 : CollatzResearch.WordTrace tailWord_585660 prefixEnd_585660 133655591161015038336269 := by
  unfold tailWord_585660
  simp only [CollatzResearch.WordTrace]
  refine ⟨10680387529130658804945217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14240516705507545073260289 10680387529130658804945217)
  ·
    refine ⟨8010290646847994103708913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10680387529130658804945217 8010290646847994103708913)
    ·
      refine ⟨6007717985135995577781685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8010290646847994103708913 6007717985135995577781685)
      ·
        refine ⟨563223561106499585417033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6007717985135995577781685 563223561106499585417033)
        ·
          refine ⟨422417670829874689062775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 563223561106499585417033 422417670829874689062775)
          ·
            refine ⟨633626506244812033594163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 422417670829874689062775 633626506244812033594163)
            ·
              refine ⟨950439759367218050391245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 633626506244812033594163 950439759367218050391245)
              ·
                refine ⟨356414909762706768896717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 950439759367218050391245 356414909762706768896717)
                ·
                  refine ⟨133655591161015038336269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 356414909762706768896717 133655591161015038336269)
                  ·
                    rfl

theorem cell21_585660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 3, 3].length) (baseStart_585660 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_585660 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_585660 prefixEnd_585660 := by exact prefixLift 585660
  have htrace : WordTrace (prefixWord ++ tailWord_585660) baseStart_585660 baseEnd_585660 := by
    simpa [prefixWord, tailWord_585660, baseEnd_585660] using wordTrace_append hprefix tailTrace_585660
  have hstable : (prefixWord ++ tailWord_585660).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585660).length < 2 ^ (prefixWord ++ tailWord_585660).sum := by decide
  have hdescent : baseEnd_585660 < baseStart_585660 := by decide
  rcases family_descends (prefixWord ++ tailWord_585660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585685 : List Nat := [1, 3, 2, 3, 2, 3, 1, 1, 5]
def baseStart_585685 : Nat := 118140960795 + 585685 * 2 ^ 59
def prefixEnd_585685 : Nat := 4983230072969 + 3 ^ 40 * 585685 * 2
def baseEnd_585685 : Nat := 133661296501620550419551

theorem tailTrace_585685 : CollatzResearch.WordTrace tailWord_585685 prefixEnd_585685 133661296501620550419551 := by
  unfold tailWord_585685
  simp only [CollatzResearch.WordTrace]
  refine ⟨21361686883170746879550509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14241124588780497919700339 21361686883170746879550509)
  ·
    refine ⟨8010632581189030079831441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21361686883170746879550509 8010632581189030079831441)
    ·
      refine ⟨6007974435891772559873581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8010632581189030079831441 6007974435891772559873581)
      ·
        refine ⟨2252990413459414709952593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6007974435891772559873581 2252990413459414709952593)
        ·
          refine ⟨1689742810094561032464445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2252990413459414709952593 1689742810094561032464445)
          ·
            refine ⟨633653553785460387174167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1689742810094561032464445 633653553785460387174167)
            ·
              refine ⟨950480330678190580761251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 633653553785460387174167 950480330678190580761251)
              ·
                refine ⟨1425720496017285871141877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 950480330678190580761251 1425720496017285871141877)
                ·
                  refine ⟨133661296501620550419551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1425720496017285871141877 133661296501620550419551)
                  ·
                    rfl

theorem cell21_585685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 1, 5].length) (baseStart_585685 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_585685 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_585685 prefixEnd_585685 := by exact prefixLift 585685
  have htrace : WordTrace (prefixWord ++ tailWord_585685) baseStart_585685 baseEnd_585685 := by
    simpa [prefixWord, tailWord_585685, baseEnd_585685] using wordTrace_append hprefix tailTrace_585685
  have hstable : (prefixWord ++ tailWord_585685).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585685).length < 2 ^ (prefixWord ++ tailWord_585685).sum := by decide
  have hdescent : baseEnd_585685 < baseStart_585685 := by decide
  rcases family_descends (prefixWord ++ tailWord_585685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585699 : List Nat := [1, 1, 1, 6, 1, 3, 1, 3, 4]
def baseStart_585699 : Nat := 118140960795 + 585699 * 2 ^ 59
def prefixEnd_585699 : Nat := 4983230072969 + 3 ^ 40 * 585699 * 2
def baseEnd_585699 : Nat := 133664491492359637186189

theorem tailTrace_585699 : CollatzResearch.WordTrace tailWord_585699 prefixEnd_585699 133664491492359637186189 := by
  unfold tailWord_585699
  simp only [CollatzResearch.WordTrace]
  refine ⟨21362197505120027270560151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14241465003413351513706767 21362197505120027270560151)
  ·
    refine ⟨32043296257680040905840227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21362197505120027270560151 32043296257680040905840227)
    ·
      refine ⟨48064944386520061358760341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32043296257680040905840227 48064944386520061358760341)
      ·
        refine ⟨2253044268118127876191891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 48064944386520061358760341 2253044268118127876191891)
        ·
          refine ⟨3379566402177191814287837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2253044268118127876191891 3379566402177191814287837)
          ·
            refine ⟨1267337400816446930357939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3379566402177191814287837 1267337400816446930357939)
            ·
              refine ⟨1901006101224670395536909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1267337400816446930357939 1901006101224670395536909)
              ·
                refine ⟨712877287959251398326341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1901006101224670395536909 712877287959251398326341)
                ·
                  refine ⟨133664491492359637186189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 712877287959251398326341 133664491492359637186189)
                  ·
                    rfl

theorem cell21_585699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 3, 4].length) (baseStart_585699 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_585699 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_585699 prefixEnd_585699 := by exact prefixLift 585699
  have htrace : WordTrace (prefixWord ++ tailWord_585699) baseStart_585699 baseEnd_585699 := by
    simpa [prefixWord, tailWord_585699, baseEnd_585699] using wordTrace_append hprefix tailTrace_585699
  have hstable : (prefixWord ++ tailWord_585699).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585699).length < 2 ^ (prefixWord ++ tailWord_585699).sum := by decide
  have hdescent : baseEnd_585699 < baseStart_585699 := by decide
  rcases family_descends (prefixWord ++ tailWord_585699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585744 : List Nat := [2, 1, 1, 1, 1, 1, 1, 10, 3]
def baseStart_585744 : Nat := 118140960795 + 585744 * 2 ^ 59
def prefixEnd_585744 : Nat := 4983230072969 + 3 ^ 40 * 585744 * 2
def baseEnd_585744 : Nat := 133674761105449558936097

theorem tailTrace_585744 : CollatzResearch.WordTrace tailWord_585744 prefixEnd_585744 133674761105449558936097 := by
  unfold tailWord_585744
  simp only [CollatzResearch.WordTrace]
  refine ⟨10681919394978499977974143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14242559193304666637298857 10681919394978499977974143)
  ·
    refine ⟨16022879092467749966961215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10681919394978499977974143 16022879092467749966961215)
    ·
      refine ⟨24034318638701624950441823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16022879092467749966961215 24034318638701624950441823)
      ·
        refine ⟨36051477958052437425662735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24034318638701624950441823 36051477958052437425662735)
        ·
          refine ⟨54077216937078656138494103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36051477958052437425662735 54077216937078656138494103)
          ·
            refine ⟨81115825405617984207741155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54077216937078656138494103 81115825405617984207741155)
            ·
              refine ⟨121673738108426976311611733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81115825405617984207741155 121673738108426976311611733)
              ·
                refine ⟨356466029614532157162925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 121673738108426976311611733 356466029614532157162925)
                ·
                  refine ⟨133674761105449558936097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 356466029614532157162925 133674761105449558936097)
                  ·
                    rfl

theorem cell21_585744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 10, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 10, 3].length) (baseStart_585744 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_585744 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_585744 prefixEnd_585744 := by exact prefixLift 585744
  have htrace : WordTrace (prefixWord ++ tailWord_585744) baseStart_585744 baseEnd_585744 := by
    simpa [prefixWord, tailWord_585744, baseEnd_585744] using wordTrace_append hprefix tailTrace_585744
  have hstable : (prefixWord ++ tailWord_585744).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585744).length < 2 ^ (prefixWord ++ tailWord_585744).sum := by decide
  have hdescent : baseEnd_585744 < baseStart_585744 := by decide
  rcases family_descends (prefixWord ++ tailWord_585744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585820 : List Nat := [2, 2, 4, 1, 1, 2, 2, 2, 5]
def baseStart_585820 : Nat := 118140960795 + 585820 * 2 ^ 59
def prefixEnd_585820 : Nat := 4983230072969 + 3 ^ 40 * 585820 * 2
def baseEnd_585820 : Nat := 133692105340890315669275

theorem tailTrace_585820 : CollatzResearch.WordTrace tailWord_585820 prefixEnd_585820 133692105340890315669275 := by
  unfold tailWord_585820
  simp only [CollatzResearch.WordTrace]
  refine ⟨10683305368840832467857457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14244407158454443290476609 10683305368840832467857457)
  ·
    refine ⟨8012479026630624350893093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10683305368840832467857457 8012479026630624350893093)
    ·
      refine ⟨1502339817493242065792455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8012479026630624350893093 1502339817493242065792455)
      ·
        refine ⟨2253509726239863098688683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1502339817493242065792455 2253509726239863098688683)
        ·
          refine ⟨3380264589359794648033025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2253509726239863098688683 3380264589359794648033025)
          ·
            refine ⟨2535198442019845986024769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3380264589359794648033025 2535198442019845986024769)
            ·
              refine ⟨1901398831514884489518577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2535198442019845986024769 1901398831514884489518577)
              ·
                refine ⟨1426049123636163367138933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1901398831514884489518577 1426049123636163367138933)
                ·
                  refine ⟨133692105340890315669275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1426049123636163367138933 133692105340890315669275)
                  ·
                    rfl

theorem cell21_585820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 2, 5].length) (baseStart_585820 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_585820 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_585820 prefixEnd_585820 := by exact prefixLift 585820
  have htrace : WordTrace (prefixWord ++ tailWord_585820) baseStart_585820 baseEnd_585820 := by
    simpa [prefixWord, tailWord_585820, baseEnd_585820] using wordTrace_append hprefix tailTrace_585820
  have hstable : (prefixWord ++ tailWord_585820).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585820).length < 2 ^ (prefixWord ++ tailWord_585820).sum := by decide
  have hdescent : baseEnd_585820 < baseStart_585820 := by decide
  rcases family_descends (prefixWord ++ tailWord_585820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586023 : List Nat := [1, 1, 8, 1, 1, 2, 1, 1, 5]
def baseStart_586023 : Nat := 118140960795 + 586023 * 2 ^ 59
def prefixEnd_586023 : Nat := 4983230072969 + 3 ^ 40 * 586023 * 2
def baseEnd_586023 : Nat := 133738432706607073785527

theorem tailTrace_586023 : CollatzResearch.WordTrace tailWord_586023 prefixEnd_586023 133738432706607073785527 := by
  unfold tailWord_586023
  simp only [CollatzResearch.WordTrace]
  refine ⟨21374014755946230605354723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14249343170630820403569815 21374014755946230605354723)
  ·
    refine ⟨32061022133919345908032085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21374014755946230605354723 32061022133919345908032085)
    ·
      refine ⟨375715103131867334859751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 32061022133919345908032085 375715103131867334859751)
      ·
        refine ⟨563572654697801002289627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 375715103131867334859751 563572654697801002289627)
        ·
          refine ⟨845358982046701503434441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 563572654697801002289627 845358982046701503434441)
          ·
            refine ⟨634019236535026127575831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 845358982046701503434441 634019236535026127575831)
            ·
              refine ⟨951028854802539191363747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 634019236535026127575831 951028854802539191363747)
              ·
                refine ⟨1426543282203808787045621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 951028854802539191363747 1426543282203808787045621)
                ·
                  refine ⟨133738432706607073785527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1426543282203808787045621 133738432706607073785527)
                  ·
                    rfl

theorem cell21_586023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 1, 5].length) (baseStart_586023 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_586023 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_586023 prefixEnd_586023 := by exact prefixLift 586023
  have htrace : WordTrace (prefixWord ++ tailWord_586023) baseStart_586023 baseEnd_586023 := by
    simpa [prefixWord, tailWord_586023, baseEnd_586023] using wordTrace_append hprefix tailTrace_586023
  have hstable : (prefixWord ++ tailWord_586023).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586023).length < 2 ^ (prefixWord ++ tailWord_586023).sum := by decide
  have hdescent : baseEnd_586023 < baseStart_586023 := by decide
  rcases family_descends (prefixWord ++ tailWord_586023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586031 : List Nat := [1, 1, 2, 1, 2, 1, 7, 1, 5]
def baseStart_586031 : Nat := 118140960795 + 586031 * 2 ^ 59
def prefixEnd_586031 : Nat := 4983230072969 + 3 ^ 40 * 586031 * 2
def baseEnd_586031 : Nat := 133740258415600837652177

theorem tailTrace_586031 : CollatzResearch.WordTrace tailWord_586031 prefixEnd_586031 133740258415600837652177 := by
  unfold tailWord_586031
  simp only [CollatzResearch.WordTrace]
  refine ⟨21374306539917247971645947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14249537693278165314430631 21374306539917247971645947)
  ·
    refine ⟨32061459809875871957468921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21374306539917247971645947 32061459809875871957468921)
    ·
      refine ⟨24046094857406903968101691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32061459809875871957468921 24046094857406903968101691)
      ·
        refine ⟨36069142286110355952152537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24046094857406903968101691 36069142286110355952152537)
        ·
          refine ⟨27051856714582766964114403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36069142286110355952152537 27051856714582766964114403)
          ·
            refine ⟨40577785071874150446171605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27051856714582766964114403 40577785071874150446171605)
            ·
              refine ⟨951041837622050401082147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 40577785071874150446171605 951041837622050401082147)
              ·
                refine ⟨1426562756433075601623221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 951041837622050401082147 1426562756433075601623221)
                ·
                  refine ⟨133740258415600837652177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1426562756433075601623221 133740258415600837652177)
                  ·
                    rfl

theorem cell21_586031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 1, 5].length) (baseStart_586031 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_586031 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_586031 prefixEnd_586031 := by exact prefixLift 586031
  have htrace : WordTrace (prefixWord ++ tailWord_586031) baseStart_586031 baseEnd_586031 := by
    simpa [prefixWord, tailWord_586031, baseEnd_586031] using wordTrace_append hprefix tailTrace_586031
  have hstable : (prefixWord ++ tailWord_586031).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586031).length < 2 ^ (prefixWord ++ tailWord_586031).sum := by decide
  have hdescent : baseEnd_586031 < baseStart_586031 := by decide
  rcases family_descends (prefixWord ++ tailWord_586031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586082 : List Nat := [3, 3, 2, 1, 1, 2, 4, 2, 3]
def baseStart_586082 : Nat := 118140960795 + 586082 * 2 ^ 59
def prefixEnd_586082 : Nat := 4983230072969 + 3 ^ 40 * 586082 * 2
def baseEnd_586082 : Nat := 133751897310436082302073

theorem tailTrace_586082 : CollatzResearch.WordTrace tailWord_586082 prefixEnd_586082 133751897310436082302073 := by
  unfold tailWord_586082
  simp only [CollatzResearch.WordTrace]
  refine ⟨5344041665683120920438125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14250777775154989121168333 5344041665683120920438125)
  ·
    refine ⟨2004015624631170345164297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5344041665683120920438125 2004015624631170345164297)
    ·
      refine ⟨1503011718473377758873223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2004015624631170345164297 1503011718473377758873223)
      ·
        refine ⟨2254517577710066638309835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1503011718473377758873223 2254517577710066638309835)
        ·
          refine ⟨3381776366565099957464753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2254517577710066638309835 3381776366565099957464753)
          ·
            refine ⟨2536332274923824968098565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3381776366565099957464753 2536332274923824968098565)
            ·
              refine ⟨475562301548217181518481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2536332274923824968098565 475562301548217181518481)
              ·
                refine ⟨356671726161162886138861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 475562301548217181518481 356671726161162886138861)
                ·
                  refine ⟨133751897310436082302073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 356671726161162886138861 133751897310436082302073)
                  ·
                    rfl

theorem cell21_586082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_586082 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_586082 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_586082 prefixEnd_586082 := by exact prefixLift 586082
  have htrace : WordTrace (prefixWord ++ tailWord_586082) baseStart_586082 baseEnd_586082 := by
    simpa [prefixWord, tailWord_586082, baseEnd_586082] using wordTrace_append hprefix tailTrace_586082
  have hstable : (prefixWord ++ tailWord_586082).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586082).length < 2 ^ (prefixWord ++ tailWord_586082).sum := by decide
  have hdescent : baseEnd_586082 < baseStart_586082 := by decide
  rcases family_descends (prefixWord ++ tailWord_586082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586107 : List Nat := [1, 1, 1, 1, 1, 8, 1, 2, 5]
def baseStart_586107 : Nat := 118140960795 + 586107 * 2 ^ 59
def prefixEnd_586107 : Nat := 4983230072969 + 3 ^ 40 * 586107 * 2
def baseEnd_586107 : Nat := 133757602651041594385355

theorem tailTrace_586107 : CollatzResearch.WordTrace tailWord_586107 prefixEnd_586107 133757602651041594385355 := by
  unfold tailWord_586107
  simp only [CollatzResearch.WordTrace]
  refine ⟨21377078487641912951412575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14251385658427941967608383 21377078487641912951412575)
  ·
    refine ⟨32065617731462869427118863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21377078487641912951412575 32065617731462869427118863)
    ·
      refine ⟨48098426597194304140678295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32065617731462869427118863 48098426597194304140678295)
      ·
        refine ⟨72147639895791456211017443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48098426597194304140678295 72147639895791456211017443)
        ·
          refine ⟨108221459843687184316526165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72147639895791456211017443 108221459843687184316526165)
          ·
            refine ⟨1268220232543209191209291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 108221459843687184316526165 1268220232543209191209291)
            ·
              refine ⟨1902330348814813786813937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1268220232543209191209291 1902330348814813786813937)
              ·
                refine ⟨1426747761611110340110453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1902330348814813786813937 1426747761611110340110453)
                ·
                  refine ⟨133757602651041594385355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1426747761611110340110453 133757602651041594385355)
                  ·
                    rfl

theorem cell21_586107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 2, 5].length) (baseStart_586107 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_586107 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_586107 prefixEnd_586107 := by exact prefixLift 586107
  have htrace : WordTrace (prefixWord ++ tailWord_586107) baseStart_586107 baseEnd_586107 := by
    simpa [prefixWord, tailWord_586107, baseEnd_586107] using wordTrace_append hprefix tailTrace_586107
  have hstable : (prefixWord ++ tailWord_586107).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586107).length < 2 ^ (prefixWord ++ tailWord_586107).sum := by decide
  have hdescent : baseEnd_586107 < baseStart_586107 := by decide
  rcases family_descends (prefixWord ++ tailWord_586107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586124 : List Nat := [2, 2, 1, 2, 1, 4, 1, 5, 3]
def baseStart_586124 : Nat := 118140960795 + 586124 * 2 ^ 59
def prefixEnd_586124 : Nat := 4983230072969 + 3 ^ 40 * 586124 * 2
def baseEnd_586124 : Nat := 133761482282653342601987

theorem tailTrace_586124 : CollatzResearch.WordTrace tailWord_586124 prefixEnd_586124 133761482282653342601987 := by
  unfold tailWord_586124
  simp only [CollatzResearch.WordTrace]
  refine ⟨10688849264290162427390713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14251799019053549903187617 10688849264290162427390713)
  ·
    refine ⟨8016636948217621820543035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10688849264290162427390713 8016636948217621820543035)
    ·
      refine ⟨12024955422326432730814553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8016636948217621820543035 12024955422326432730814553)
      ·
        refine ⟨9018716566744824548110915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12024955422326432730814553 9018716566744824548110915)
        ·
          refine ⟨13528074850117236822166373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9018716566744824548110915 13528074850117236822166373)
          ·
            refine ⟨2536514034396981904156195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13528074850117236822166373 2536514034396981904156195)
            ·
              refine ⟨3804771051595472856234293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2536514034396981904156195 3804771051595472856234293)
              ·
                refine ⟨356697286087075580271965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3804771051595472856234293 356697286087075580271965)
                ·
                  refine ⟨133761482282653342601987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 356697286087075580271965 133761482282653342601987)
                  ·
                    rfl

theorem cell21_586124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 5, 3].length) (baseStart_586124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_586124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_586124 prefixEnd_586124 := by exact prefixLift 586124
  have htrace : WordTrace (prefixWord ++ tailWord_586124) baseStart_586124 baseEnd_586124 := by
    simpa [prefixWord, tailWord_586124, baseEnd_586124] using wordTrace_append hprefix tailTrace_586124
  have hstable : (prefixWord ++ tailWord_586124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586124).length < 2 ^ (prefixWord ++ tailWord_586124).sum := by decide
  have hdescent : baseEnd_586124 < baseStart_586124 := by decide
  rcases family_descends (prefixWord ++ tailWord_586124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586138 : List Nat := [3, 1, 1, 4, 1, 3, 1, 1, 6]
def baseStart_586138 : Nat := 118140960795 + 586138 * 2 ^ 59
def prefixEnd_586138 : Nat := 4983230072969 + 3 ^ 40 * 586138 * 2
def baseEnd_586138 : Nat := 133764677273392429368625

theorem tailTrace_586138 : CollatzResearch.WordTrace tailWord_586138 prefixEnd_586138 133764677273392429368625 := by
  unfold tailWord_586138
  simp only [CollatzResearch.WordTrace]
  refine ⟨5344552287632401311447767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14252139433686403497194045 5344552287632401311447767)
  ·
    refine ⟨8016828431448601967171651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5344552287632401311447767 8016828431448601967171651)
    ·
      refine ⟨12025242647172902950757477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8016828431448601967171651 12025242647172902950757477)
      ·
        refine ⟨2254732996344919303267027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12025242647172902950757477 2254732996344919303267027)
        ·
          refine ⟨3382099494517378954900541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2254732996344919303267027 3382099494517378954900541)
          ·
            refine ⟨1268287310444017108087703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3382099494517378954900541 1268287310444017108087703)
            ·
              refine ⟨1902430965666025662131555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1268287310444017108087703 1902430965666025662131555)
              ·
                refine ⟨2853646448499038493197333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1902430965666025662131555 2853646448499038493197333)
                ·
                  refine ⟨133764677273392429368625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2853646448499038493197333 133764677273392429368625)
                  ·
                    rfl

theorem cell21_586138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 6].length) (baseStart_586138 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_586138 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_586138 prefixEnd_586138 := by exact prefixLift 586138
  have htrace : WordTrace (prefixWord ++ tailWord_586138) baseStart_586138 baseEnd_586138 := by
    simpa [prefixWord, tailWord_586138, baseEnd_586138] using wordTrace_append hprefix tailTrace_586138
  have hstable : (prefixWord ++ tailWord_586138).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586138).length < 2 ^ (prefixWord ++ tailWord_586138).sum := by decide
  have hdescent : baseEnd_586138 < baseStart_586138 := by decide
  rcases family_descends (prefixWord ++ tailWord_586138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586169 : List Nat := [1, 2, 1, 4, 3, 1, 4, 5]
def baseStart_586169 : Nat := 118140960795 + 586169 * 2 ^ 59
def prefixEnd_586169 : Nat := 4983230072969 + 3 ^ 40 * 586169 * 2
def baseEnd_586169 : Nat := 44590583965247754783965

theorem tailTrace_586169 : CollatzResearch.WordTrace tailWord_586169 prefixEnd_586169 44590583965247754783965 := by
  unfold tailWord_586169
  simp only [CollatzResearch.WordTrace]
  refine ⟨21379339813417297540169561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14252893208944865026779707 21379339813417297540169561)
  ·
    refine ⟨16034504860062973155127171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21379339813417297540169561 16034504860062973155127171)
    ·
      refine ⟨24051757290094459732690757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16034504860062973155127171 24051757290094459732690757)
      ·
        refine ⟨4509704491892711199879517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24051757290094459732690757 4509704491892711199879517)
        ·
          refine ⟨1691139184459766699954819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4509704491892711199879517 1691139184459766699954819)
          ·
            refine ⟨2536708776689650049932229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1691139184459766699954819 2536708776689650049932229)
            ·
              refine ⟨475632895629309384362293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2536708776689650049932229 475632895629309384362293)
              ·
                refine ⟨44590583965247754783965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 475632895629309384362293 44590583965247754783965)
                ·
                  rfl

theorem cell21_586169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 5].length) (baseStart_586169 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_586169 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_586169 prefixEnd_586169 := by exact prefixLift 586169
  have htrace : WordTrace (prefixWord ++ tailWord_586169) baseStart_586169 baseEnd_586169 := by
    simpa [prefixWord, tailWord_586169, baseEnd_586169] using wordTrace_append hprefix tailTrace_586169
  have hstable : (prefixWord ++ tailWord_586169).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586169).length < 2 ^ (prefixWord ++ tailWord_586169).sum := by decide
  have hdescent : baseEnd_586169 < baseStart_586169 := by decide
  rcases family_descends (prefixWord ++ tailWord_586169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586279 : List Nat := [1, 1, 7, 2, 1, 1, 3, 5]
def baseStart_586279 : Nat := 118140960795 + 586279 * 2 ^ 59
def prefixEnd_586279 : Nat := 4983230072969 + 3 ^ 40 * 586279 * 2
def baseEnd_586279 : Nat := 44598951798135839172779

theorem tailTrace_586279 : CollatzResearch.WordTrace tailWord_586279 prefixEnd_586279 44598951798135839172779 := by
  unfold tailWord_586279
  simp only [CollatzResearch.WordTrace]
  refine ⟨21383351843018786326673891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14255567895345857551115927 21383351843018786326673891)
  ·
    refine ⟨32075027764528179490010837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21383351843018786326673891 32075027764528179490010837)
    ·
      refine ⟨751758463231129206797129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 32075027764528179490010837 751758463231129206797129)
      ·
        refine ⟨563818847423346905097847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 751758463231129206797129 563818847423346905097847)
        ·
          refine ⟨845728271135020357646771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 563818847423346905097847 845728271135020357646771)
          ·
            refine ⟨1268592406702530536470157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 845728271135020357646771 1268592406702530536470157)
            ·
              refine ⟨475722152513448951176309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1268592406702530536470157 475722152513448951176309)
              ·
                refine ⟨44598951798135839172779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 475722152513448951176309 44598951798135839172779)
                ·
                  rfl

theorem cell21_586279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 5].length) (baseStart_586279 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_586279 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_586279 prefixEnd_586279 := by exact prefixLift 586279
  have htrace : WordTrace (prefixWord ++ tailWord_586279) baseStart_586279 baseEnd_586279 := by
    simpa [prefixWord, tailWord_586279, baseEnd_586279] using wordTrace_append hprefix tailTrace_586279
  have hstable : (prefixWord ++ tailWord_586279).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586279).length < 2 ^ (prefixWord ++ tailWord_586279).sum := by decide
  have hdescent : baseEnd_586279 < baseStart_586279 := by decide
  rcases family_descends (prefixWord ++ tailWord_586279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586310 : List Nat := [6, 1, 1, 1, 2, 1, 2, 4, 3]
def baseStart_586310 : Nat := 118140960795 + 586310 * 2 ^ 59
def prefixEnd_586310 : Nat := 4983230072969 + 3 ^ 40 * 586310 * 2
def baseEnd_586310 : Nat := 133803930016758352501607

theorem tailTrace_586310 : CollatzResearch.WordTrace tailWord_586310 prefixEnd_586310 133803930016758352501607 := by
  unfold tailWord_586310
  simp only [CollatzResearch.WordTrace]
  refine ⟨668265078309577456907887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14256321670604319080701589 668265078309577456907887)
  ·
    refine ⟨1002397617464366185361831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 668265078309577456907887 1002397617464366185361831)
    ·
      refine ⟨1503596426196549278042747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1002397617464366185361831 1503596426196549278042747)
      ·
        refine ⟨2255394639294823917064121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1503596426196549278042747 2255394639294823917064121)
        ·
          refine ⟨1691545979471117937798091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2255394639294823917064121 1691545979471117937798091)
          ·
            refine ⟨2537318969206676906697137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1691545979471117937798091 2537318969206676906697137)
            ·
              refine ⟨1902989226905007680022853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2537318969206676906697137 1902989226905007680022853)
              ·
                refine ⟨356810480044688940004285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1902989226905007680022853 356810480044688940004285)
                ·
                  refine ⟨133803930016758352501607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 356810480044688940004285 133803930016758352501607)
                  ·
                    rfl

theorem cell21_586310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_586310 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_586310 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_586310 prefixEnd_586310 := by exact prefixLift 586310
  have htrace : WordTrace (prefixWord ++ tailWord_586310) baseStart_586310 baseEnd_586310 := by
    simpa [prefixWord, tailWord_586310, baseEnd_586310] using wordTrace_append hprefix tailTrace_586310
  have hstable : (prefixWord ++ tailWord_586310).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586310).length < 2 ^ (prefixWord ++ tailWord_586310).sum := by decide
  have hdescent : baseEnd_586310 < baseStart_586310 := by decide
  rcases family_descends (prefixWord ++ tailWord_586310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586338 : List Nat := [3, 3, 2, 3, 1, 1, 1, 7]
def baseStart_586338 : Nat := 118140960795 + 586338 * 2 ^ 59
def prefixEnd_586338 : Nat := 4983230072969 + 3 ^ 40 * 586338 * 2
def baseEnd_586338 : Nat := 44603439999412175344961

theorem tailTrace_586338 : CollatzResearch.WordTrace tailWord_586338 prefixEnd_586338 44603439999412175344961 := by
  unfold tailWord_586338
  simp only [CollatzResearch.WordTrace]
  refine ⟨5346375937451259850767917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14257002499870026268714445 5346375937451259850767917)
  ·
    refine ⟨2004890976544222444037969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5346375937451259850767917 2004890976544222444037969)
    ·
      refine ⟨1503668232408166833028477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2004890976544222444037969 1503668232408166833028477)
      ·
        refine ⟨563875587153062562385679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1503668232408166833028477 563875587153062562385679)
        ·
          refine ⟨845813380729593843578519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 563875587153062562385679 845813380729593843578519)
          ·
            refine ⟨1268720071094390765367779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 845813380729593843578519 1268720071094390765367779)
            ·
              refine ⟨1903080106641586148051669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1268720071094390765367779 1903080106641586148051669)
              ·
                refine ⟨44603439999412175344961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1903080106641586148051669 44603439999412175344961)
                ·
                  rfl

theorem cell21_586338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 7].length) (baseStart_586338 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_586338 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_586338 prefixEnd_586338 := by exact prefixLift 586338
  have htrace : WordTrace (prefixWord ++ tailWord_586338) baseStart_586338 baseEnd_586338 := by
    simpa [prefixWord, tailWord_586338, baseEnd_586338] using wordTrace_append hprefix tailTrace_586338
  have hstable : (prefixWord ++ tailWord_586338).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586338).length < 2 ^ (prefixWord ++ tailWord_586338).sum := by decide
  have hdescent : baseEnd_586338 < baseStart_586338 := by decide
  rcases family_descends (prefixWord ++ tailWord_586338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586369 : List Nat := [1, 2, 4, 2, 1, 1, 5, 2, 3]
def baseStart_586369 : Nat := 118140960795 + 586369 * 2 ^ 59
def prefixEnd_586369 : Nat := 4983230072969 + 3 ^ 40 * 586369 * 2
def baseEnd_586369 : Nat := 133817394620587361018153

theorem tailTrace_586369 : CollatzResearch.WordTrace tailWord_586369 prefixEnd_586369 133817394620587361018153 := by
  unfold tailWord_586369
  simp only [CollatzResearch.WordTrace]
  refine ⟨21386634412692731697450161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14257756275128487798300107 21386634412692731697450161)
  ·
    refine ⟨16039975809519548773087621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21386634412692731697450161 16039975809519548773087621)
    ·
      refine ⟨3007495464284915394953929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16039975809519548773087621 3007495464284915394953929)
      ·
        refine ⟨2255621598213686546215447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3007495464284915394953929 2255621598213686546215447)
        ·
          refine ⟨3383432397320529819323171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2255621598213686546215447 3383432397320529819323171)
          ·
            refine ⟨5075148595980794728984757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3383432397320529819323171 5075148595980794728984757)
            ·
              refine ⟨475795180873199505842321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5075148595980794728984757 475795180873199505842321)
              ·
                refine ⟨356846385654899629381741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 475795180873199505842321 356846385654899629381741)
                ·
                  refine ⟨133817394620587361018153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 356846385654899629381741 133817394620587361018153)
                  ·
                    rfl

theorem cell21_586369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 2, 3].length) (baseStart_586369 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_586369 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_586369 prefixEnd_586369 := by exact prefixLift 586369
  have htrace : WordTrace (prefixWord ++ tailWord_586369) baseStart_586369 baseEnd_586369 := by
    simpa [prefixWord, tailWord_586369, baseEnd_586369] using wordTrace_append hprefix tailTrace_586369
  have hstable : (prefixWord ++ tailWord_586369).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586369).length < 2 ^ (prefixWord ++ tailWord_586369).sum := by decide
  have hdescent : baseEnd_586369 < baseStart_586369 := by decide
  rcases family_descends (prefixWord ++ tailWord_586369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586428 : List Nat := [2, 2, 2, 3, 1, 1, 3, 4, 3]
def baseStart_586428 : Nat := 118140960795 + 586428 * 2 ^ 59
def prefixEnd_586428 : Nat := 4983230072969 + 3 ^ 40 * 586428 * 2
def baseEnd_586428 : Nat := 133830859224416369534699

theorem tailTrace_586428 : CollatzResearch.WordTrace tailWord_586428 prefixEnd_586428 133830859224416369534699 := by
  unfold tailWord_586428
  simp only [CollatzResearch.WordTrace]
  refine ⟨10694393159739492386923969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14259190879652656515898625 10694393159739492386923969)
  ·
    refine ⟨8020794869804619290192977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10694393159739492386923969 8020794869804619290192977)
    ·
      refine ⟨6015596152353464467644733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8020794869804619290192977 6015596152353464467644733)
      ·
        refine ⟨2255848557132549175366775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6015596152353464467644733 2255848557132549175366775)
        ·
          refine ⟨3383772835698823763050163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2255848557132549175366775 3383772835698823763050163)
          ·
            refine ⟨5075659253548235644575245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3383772835698823763050163 5075659253548235644575245)
            ·
              refine ⟨1903372220080588366715717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5075659253548235644575245 1903372220080588366715717)
              ·
                refine ⟨356882291265110318759197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1903372220080588366715717 356882291265110318759197)
                ·
                  refine ⟨133830859224416369534699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 356882291265110318759197 133830859224416369534699)
                  ·
                    rfl

theorem cell21_586428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 4, 3].length) (baseStart_586428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_586428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_586428 prefixEnd_586428 := by exact prefixLift 586428
  have htrace : WordTrace (prefixWord ++ tailWord_586428) baseStart_586428 baseEnd_586428 := by
    simpa [prefixWord, tailWord_586428, baseEnd_586428] using wordTrace_append hprefix tailTrace_586428
  have hstable : (prefixWord ++ tailWord_586428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586428).length < 2 ^ (prefixWord ++ tailWord_586428).sum := by decide
  have hdescent : baseEnd_586428 < baseStart_586428 := by decide
  rcases family_descends (prefixWord ++ tailWord_586428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586439 : List Nat := [1, 1, 4, 1, 1, 1, 2, 10]
def baseStart_586439 : Nat := 118140960795 + 586439 * 2 ^ 59
def prefixEnd_586439 : Nat := 4983230072969 + 3 ^ 40 * 586439 * 2
def baseEnd_586439 : Nat := 44611123191427598283781

theorem tailTrace_586439 : CollatzResearch.WordTrace tailWord_586439 prefixEnd_586439 44611123191427598283781 := by
  unfold tailWord_586439
  simp only [CollatzResearch.WordTrace]
  refine ⟨21389187522439133652498371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14259458348292755768332247 21389187522439133652498371)
  ·
    refine ⟨32083781283658700478747557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21389187522439133652498371 32083781283658700478747557)
    ·
      refine ⟨6015708990686006339765167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32083781283658700478747557 6015708990686006339765167)
      ·
        refine ⟨9023563486029009509647751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6015708990686006339765167 9023563486029009509647751)
        ·
          refine ⟨13535345229043514264471627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9023563486029009509647751 13535345229043514264471627)
          ·
            refine ⟨20303017843565271396707441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13535345229043514264471627 20303017843565271396707441)
            ·
              refine ⟨15227263382673953547530581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20303017843565271396707441 15227263382673953547530581)
              ·
                refine ⟨44611123191427598283781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 15227263382673953547530581 44611123191427598283781)
                ·
                  rfl

theorem cell21_586439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 10].length) (baseStart_586439 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_586439 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_586439 prefixEnd_586439 := by exact prefixLift 586439
  have htrace : WordTrace (prefixWord ++ tailWord_586439) baseStart_586439 baseEnd_586439 := by
    simpa [prefixWord, tailWord_586439, baseEnd_586439] using wordTrace_append hprefix tailTrace_586439
  have hstable : (prefixWord ++ tailWord_586439).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586439).length < 2 ^ (prefixWord ++ tailWord_586439).sum := by decide
  have hdescent : baseEnd_586439 < baseStart_586439 := by decide
  rcases family_descends (prefixWord ++ tailWord_586439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586442 : List Nat := [3, 1, 2, 1, 4, 1, 2, 3, 4]
def baseStart_586442 : Nat := 118140960795 + 586442 * 2 ^ 59
def prefixEnd_586442 : Nat := 4983230072969 + 3 ^ 40 * 586442 * 2
def baseEnd_586442 : Nat := 133834054215155456301337

theorem tailTrace_586442 : CollatzResearch.WordTrace tailWord_586442 prefixEnd_586442 133834054215155456301337 := by
  unfold tailWord_586442
  simp only [CollatzResearch.WordTrace]
  refine ⟨5347324235357066291214395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14259531294285510109905053 5347324235357066291214395)
  ·
    refine ⟨8020986353035599436821593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5347324235357066291214395 8020986353035599436821593)
    ·
      refine ⟨6015739764776699577616195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8020986353035599436821593 6015739764776699577616195)
      ·
        refine ⟨9023609647165049366424293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6015739764776699577616195 9023609647165049366424293)
        ·
          refine ⟨1691926808843446756204555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9023609647165049366424293 1691926808843446756204555)
          ·
            refine ⟨2537890213265170134306833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1691926808843446756204555 2537890213265170134306833)
            ·
              refine ⟨1903417659948877600730125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2537890213265170134306833 1903417659948877600730125)
              ·
                refine ⟨713781622480829100273797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1903417659948877600730125 713781622480829100273797)
                ·
                  refine ⟨133834054215155456301337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 713781622480829100273797 133834054215155456301337)
                  ·
                    rfl

theorem cell21_586442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 3, 4].length) (baseStart_586442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_586442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_586442 prefixEnd_586442 := by exact prefixLift 586442
  have htrace : WordTrace (prefixWord ++ tailWord_586442) baseStart_586442 baseEnd_586442 := by
    simpa [prefixWord, tailWord_586442, baseEnd_586442] using wordTrace_append hprefix tailTrace_586442
  have hstable : (prefixWord ++ tailWord_586442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586442).length < 2 ^ (prefixWord ++ tailWord_586442).sum := by decide
  have hdescent : baseEnd_586442 < baseStart_586442 := by decide
  rcases family_descends (prefixWord ++ tailWord_586442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586445 : List Nat := [1, 6, 2, 1, 2, 1, 1, 2, 5]
def baseStart_586445 : Nat := 118140960795 + 586445 * 2 ^ 59
def prefixEnd_586445 : Nat := 4983230072969 + 3 ^ 40 * 586445 * 2
def baseEnd_586445 : Nat := 133834738856028117751331

theorem tailTrace_586445 : CollatzResearch.WordTrace tailWord_586445 prefixEnd_586445 133834738856028117751331 := by
  unfold tailWord_586445
  simp only [CollatzResearch.WordTrace]
  refine ⟨21389406360417396677216789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14259604240278264451477859 21389406360417396677216789)
  ·
    refine ⟨1002628423144565469244537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 21389406360417396677216789 1002628423144565469244537)
    ·
      refine ⟨751971317358424101933403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1002628423144565469244537 751971317358424101933403)
      ·
        refine ⟨1127956976037636152900105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 751971317358424101933403 1127956976037636152900105)
        ·
          refine ⟨845967732028227114675079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1127956976037636152900105 845967732028227114675079)
          ·
            refine ⟨1268951598042340672012619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 845967732028227114675079 1268951598042340672012619)
            ·
              refine ⟨1903427397063511008018929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1268951598042340672012619 1903427397063511008018929)
              ·
                refine ⟨1427570547797633256014197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1903427397063511008018929 1427570547797633256014197)
                ·
                  refine ⟨133834738856028117751331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1427570547797633256014197 133834738856028117751331)
                  ·
                    rfl

theorem cell21_586445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_586445 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_586445 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_586445 prefixEnd_586445 := by exact prefixLift 586445
  have htrace : WordTrace (prefixWord ++ tailWord_586445) baseStart_586445 baseEnd_586445 := by
    simpa [prefixWord, tailWord_586445, baseEnd_586445] using wordTrace_append hprefix tailTrace_586445
  have hstable : (prefixWord ++ tailWord_586445).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586445).length < 2 ^ (prefixWord ++ tailWord_586445).sum := by decide
  have hdescent : baseEnd_586445 < baseStart_586445 := by decide
  rcases family_descends (prefixWord ++ tailWord_586445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586501 : List Nat := [1, 3, 1, 1, 2, 1, 1, 7, 4]
def baseStart_586501 : Nat := 118140960795 + 586501 * 2 ^ 59
def prefixEnd_586501 : Nat := 4983230072969 + 3 ^ 40 * 586501 * 2
def baseEnd_586501 : Nat := 133847518818984464817883

theorem tailTrace_586501 : CollatzResearch.WordTrace tailWord_586501 prefixEnd_586501 133847518818984464817883 := by
  unfold tailWord_586501
  simp only [CollatzResearch.WordTrace]
  refine ⟨21391448848214518241255357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14260965898809678827503571 21391448848214518241255357)
  ·
    refine ⟨8021793318080444340470759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21391448848214518241255357 8021793318080444340470759)
    ·
      refine ⟨12032689977120666510706139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8021793318080444340470759 12032689977120666510706139)
      ·
        refine ⟨18049034965680999766059209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12032689977120666510706139 18049034965680999766059209)
        ·
          refine ⟨13536776224260749824544407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18049034965680999766059209 13536776224260749824544407)
          ·
            refine ⟨20305164336391124736816611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13536776224260749824544407 20305164336391124736816611)
            ·
              refine ⟨30457746504586687105224917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20305164336391124736816611 30457746504586687105224917)
              ·
                refine ⟨713853433701250479028709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 30457746504586687105224917 713853433701250479028709)
                ·
                  refine ⟨133847518818984464817883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 713853433701250479028709 133847518818984464817883)
                  ·
                    rfl

theorem cell21_586501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 7, 4].length) (baseStart_586501 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_586501 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_586501 prefixEnd_586501 := by exact prefixLift 586501
  have htrace : WordTrace (prefixWord ++ tailWord_586501) baseStart_586501 baseEnd_586501 := by
    simpa [prefixWord, tailWord_586501, baseEnd_586501] using wordTrace_append hprefix tailTrace_586501
  have hstable : (prefixWord ++ tailWord_586501).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586501).length < 2 ^ (prefixWord ++ tailWord_586501).sum := by decide
  have hdescent : baseEnd_586501 < baseStart_586501 := by decide
  rcases family_descends (prefixWord ++ tailWord_586501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586515 : List Nat := [1, 1, 1, 2, 1, 3, 5, 7]
def baseStart_586515 : Nat := 118140960795 + 586515 * 2 ^ 59
def prefixEnd_586515 : Nat := 4983230072969 + 3 ^ 40 * 586515 * 2
def baseEnd_586515 : Nat := 44616904603241183861507

theorem tailTrace_586515 : CollatzResearch.WordTrace tailWord_586515 prefixEnd_586515 44616904603241183861507 := by
  unfold tailWord_586515
  simp only [CollatzResearch.WordTrace]
  refine ⟨21391959470163798632264999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14261306313442532421509999 21391959470163798632264999)
  ·
    refine ⟨32087939205245697948397499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21391959470163798632264999 32087939205245697948397499)
    ·
      refine ⟨48131908807868546922596249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32087939205245697948397499 48131908807868546922596249)
      ·
        refine ⟨36098931605901410191947187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48131908807868546922596249 36098931605901410191947187)
        ·
          refine ⟨54148397408852115287920781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36098931605901410191947187 54148397408852115287920781)
          ·
            refine ⟨20305649028319543232970293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54148397408852115287920781 20305649028319543232970293)
            ·
              refine ⟨1903654596404957178090965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20305649028319543232970293 1903654596404957178090965)
              ·
                refine ⟨44616904603241183861507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1903654596404957178090965 44616904603241183861507)
                ·
                  rfl

theorem cell21_586515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 7].length) (baseStart_586515 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_586515 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_586515 prefixEnd_586515 := by exact prefixLift 586515
  have htrace : WordTrace (prefixWord ++ tailWord_586515) baseStart_586515 baseEnd_586515 := by
    simpa [prefixWord, tailWord_586515, baseEnd_586515] using wordTrace_append hprefix tailTrace_586515
  have hstable : (prefixWord ++ tailWord_586515).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586515).length < 2 ^ (prefixWord ++ tailWord_586515).sum := by decide
  have hdescent : baseEnd_586515 < baseStart_586515 := by decide
  rcases family_descends (prefixWord ++ tailWord_586515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586538 : List Nat := [3, 1, 4, 3, 2, 1, 1, 1, 5]
def baseStart_586538 : Nat := 118140960795 + 586538 * 2 ^ 59
def prefixEnd_586538 : Nat := 4983230072969 + 3 ^ 40 * 586538 * 2
def baseEnd_586538 : Nat := 133855962723080622701141

theorem tailTrace_586538 : CollatzResearch.WordTrace tailWord_586538 prefixEnd_586538 133855962723080622701141 := by
  unfold tailWord_586538
  simp only [CollatzResearch.WordTrace]
  refine ⟨5348199587270118390088067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14261865566053649040234845 5348199587270118390088067)
  ·
    refine ⟨8022299380905177585132101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5348199587270118390088067 8022299380905177585132101)
    ·
      refine ⟨1504181133919720797212269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8022299380905177585132101 1504181133919720797212269)
      ·
        refine ⟨564067925219895298954601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1504181133919720797212269 564067925219895298954601)
        ·
          refine ⟨423050943914921474215951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 564067925219895298954601 423050943914921474215951)
          ·
            refine ⟨634576415872382211323927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 423050943914921474215951 634576415872382211323927)
            ·
              refine ⟨951864623808573316985891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 634576415872382211323927 951864623808573316985891)
              ·
                refine ⟨1427796935712859975478837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 951864623808573316985891 1427796935712859975478837)
                ·
                  refine ⟨133855962723080622701141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1427796935712859975478837 133855962723080622701141)
                  ·
                    rfl

theorem cell21_586538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 1, 5].length) (baseStart_586538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_586538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_586538 prefixEnd_586538 := by exact prefixLift 586538
  have htrace : WordTrace (prefixWord ++ tailWord_586538) baseStart_586538 baseEnd_586538 := by
    simpa [prefixWord, tailWord_586538, baseEnd_586538] using wordTrace_append hprefix tailTrace_586538
  have hstable : (prefixWord ++ tailWord_586538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586538).length < 2 ^ (prefixWord ++ tailWord_586538).sum := by decide
  have hdescent : baseEnd_586538 < baseStart_586538 := by decide
  rcases family_descends (prefixWord ++ tailWord_586538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586653 : List Nat := [1, 4, 2, 1, 2, 1, 3, 1, 6]
def baseStart_586653 : Nat := 118140960795 + 586653 * 2 ^ 59
def prefixEnd_586653 : Nat := 4983230072969 + 3 ^ 40 * 586653 * 2
def baseEnd_586653 : Nat := 133882207289865978284239

theorem tailTrace_586653 : CollatzResearch.WordTrace tailWord_586653 prefixEnd_586653 133882207289865978284239 := by
  unfold tailWord_586653
  simp only [CollatzResearch.WordTrace]
  refine ⟨21396992743663848200788613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14264661829109232133859075 21396992743663848200788613)
  ·
    refine ⟨4011936139436971537647865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21396992743663848200788613 4011936139436971537647865)
    ·
      refine ⟨3008952104577728653235899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4011936139436971537647865 3008952104577728653235899)
      ·
        refine ⟨4513428156866592979853849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3008952104577728653235899 4513428156866592979853849)
        ·
          refine ⟨3385071117649944734890387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4513428156866592979853849 3385071117649944734890387)
          ·
            refine ⟨5077606676474917102335581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3385071117649944734890387 5077606676474917102335581)
            ·
              refine ⟨1904102503678093913375843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5077606676474917102335581 1904102503678093913375843)
              ·
                refine ⟨2856153755517140870063765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1904102503678093913375843 2856153755517140870063765)
                ·
                  refine ⟨133882207289865978284239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2856153755517140870063765 133882207289865978284239)
                  ·
                    rfl

theorem cell21_586653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_586653 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_586653 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_586653 prefixEnd_586653 := by exact prefixLift 586653
  have htrace : WordTrace (prefixWord ++ tailWord_586653) baseStart_586653 baseEnd_586653 := by
    simpa [prefixWord, tailWord_586653, baseEnd_586653] using wordTrace_append hprefix tailTrace_586653
  have hstable : (prefixWord ++ tailWord_586653).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586653).length < 2 ^ (prefixWord ++ tailWord_586653).sum := by decide
  have hdescent : baseEnd_586653 < baseStart_586653 := by decide
  rcases family_descends (prefixWord ++ tailWord_586653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586791 : List Nat := [1, 1, 7, 1, 1, 1, 1, 1, 7]
def baseStart_586791 : Nat := 118140960795 + 586791 * 2 ^ 59
def prefixEnd_586791 : Nat := 4983230072969 + 3 ^ 40 * 586791 * 2
def baseEnd_586791 : Nat := 133913700770008404983957

theorem tailTrace_586791 : CollatzResearch.WordTrace tailWord_586791 prefixEnd_586791 133913700770008404983957 := by
  unfold tailWord_586791
  simp only [CollatzResearch.WordTrace]
  refine ⟨21402026017163897769312227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14268017344775931846208151 21402026017163897769312227)
  ·
    refine ⟨32103039025745846653968341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21402026017163897769312227 32103039025745846653968341)
    ·
      refine ⟨752414977165918280952383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 32103039025745846653968341 752414977165918280952383)
      ·
        refine ⟨1128622465748877421428575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 752414977165918280952383 1128622465748877421428575)
        ·
          refine ⟨1692933698623316132142863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1128622465748877421428575 1692933698623316132142863)
          ·
            refine ⟨2539400547934974198214295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1692933698623316132142863 2539400547934974198214295)
            ·
              refine ⟨3809100821902461297321443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2539400547934974198214295 3809100821902461297321443)
              ·
                refine ⟨5713651232853691945982165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3809100821902461297321443 5713651232853691945982165)
                ·
                  refine ⟨133913700770008404983957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5713651232853691945982165 133913700770008404983957)
                  ·
                    rfl

theorem cell21_586791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 7].length) (baseStart_586791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_586791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_586791 prefixEnd_586791 := by exact prefixLift 586791
  have htrace : WordTrace (prefixWord ++ tailWord_586791) baseStart_586791 baseEnd_586791 := by
    simpa [prefixWord, tailWord_586791, baseEnd_586791] using wordTrace_append hprefix tailTrace_586791
  have hstable : (prefixWord ++ tailWord_586791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586791).length < 2 ^ (prefixWord ++ tailWord_586791).sum := by decide
  have hdescent : baseEnd_586791 < baseStart_586791 := by decide
  rcases family_descends (prefixWord ++ tailWord_586791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586808 : List Nat := [2, 1, 2, 1, 5, 2, 2, 3, 3]
def baseStart_586808 : Nat := 118140960795 + 586808 * 2 ^ 59
def prefixEnd_586808 : Nat := 4983230072969 + 3 ^ 40 * 586808 * 2
def baseEnd_586808 : Nat := 133917580401620153200589

theorem tailTrace_586808 : CollatzResearch.WordTrace tailWord_586808 prefixEnd_586808 133917580401620153200589 := by
  unfold tailWord_586808
  simp only [CollatzResearch.WordTrace]
  refine ⟨10701323029051154836340539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14268430705401539781787385 10701323029051154836340539)
  ·
    refine ⟨16051984543576732254510809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10701323029051154836340539 16051984543576732254510809)
    ·
      refine ⟨12038988407682549190883107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16051984543576732254510809 12038988407682549190883107)
      ·
        refine ⟨18058482611523823786324661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12038988407682549190883107 18058482611523823786324661)
        ·
          refine ⟨1692982744830358479967937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18058482611523823786324661 1692982744830358479967937)
          ·
            refine ⟨1269737058622768859975953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1692982744830358479967937 1269737058622768859975953)
            ·
              refine ⟨952302793967076644981965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1269737058622768859975953 952302793967076644981965)
              ·
                refine ⟨357113547737653741868237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 952302793967076644981965 357113547737653741868237)
                ·
                  refine ⟨133917580401620153200589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 357113547737653741868237 133917580401620153200589)
                  ·
                    rfl

theorem cell21_586808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 3, 3].length) (baseStart_586808 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_586808 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_586808 prefixEnd_586808 := by exact prefixLift 586808
  have htrace : WordTrace (prefixWord ++ tailWord_586808) baseStart_586808 baseEnd_586808 := by
    simpa [prefixWord, tailWord_586808, baseEnd_586808] using wordTrace_append hprefix tailTrace_586808
  have hstable : (prefixWord ++ tailWord_586808).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586808).length < 2 ^ (prefixWord ++ tailWord_586808).sum := by decide
  have hdescent : baseEnd_586808 < baseStart_586808 := by decide
  rcases family_descends (prefixWord ++ tailWord_586808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586864 : List Nat := [2, 1, 1, 1, 5, 1, 1, 1, 8]
def baseStart_586864 : Nat := 118140960795 + 586864 * 2 ^ 59
def prefixEnd_586864 : Nat := 4983230072969 + 3 ^ 40 * 586864 * 2
def baseEnd_586864 : Nat := 133930360364576500267141

theorem tailTrace_586864 : CollatzResearch.WordTrace tailWord_586864 prefixEnd_586864 133930360364576500267141 := by
  unfold tailWord_586864
  simp only [CollatzResearch.WordTrace]
  refine ⟨10702344272949715618359823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14269792363932954157813097 10702344272949715618359823)
  ·
    refine ⟨16053516409424573427539735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10702344272949715618359823 16053516409424573427539735)
    ·
      refine ⟨24080274614136860141309603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16053516409424573427539735 24080274614136860141309603)
      ·
        refine ⟨36120411921205290211964405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24080274614136860141309603 36120411921205290211964405)
        ·
          refine ⟨3386288617612995957371663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36120411921205290211964405 3386288617612995957371663)
          ·
            refine ⟨5079432926419493936057495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3386288617612995957371663 5079432926419493936057495)
            ·
              refine ⟨7619149389629240904086243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5079432926419493936057495 7619149389629240904086243)
              ·
                refine ⟨11428724084443861356129365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7619149389629240904086243 11428724084443861356129365)
                ·
                  refine ⟨133930360364576500267141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11428724084443861356129365 133930360364576500267141)
                  ·
                    rfl

theorem cell21_586864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 8].length) (baseStart_586864 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_586864 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_586864 prefixEnd_586864 := by exact prefixLift 586864
  have htrace : WordTrace (prefixWord ++ tailWord_586864) baseStart_586864 baseEnd_586864 := by
    simpa [prefixWord, tailWord_586864, baseEnd_586864] using wordTrace_append hprefix tailTrace_586864
  have hstable : (prefixWord ++ tailWord_586864).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586864).length < 2 ^ (prefixWord ++ tailWord_586864).sum := by decide
  have hdescent : baseEnd_586864 < baseStart_586864 := by decide
  rcases family_descends (prefixWord ++ tailWord_586864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586881 : List Nat := [1, 2, 4, 2, 2, 1, 2, 1, 6]
def baseStart_586881 : Nat := 118140960795 + 586881 * 2 ^ 59
def prefixEnd_586881 : Nat := 4983230072969 + 3 ^ 40 * 586881 * 2
def baseEnd_586881 : Nat := 133934239996188248483773

theorem tailTrace_586881 : CollatzResearch.WordTrace tailWord_586881 prefixEnd_586881 133934239996188248483773 := by
  unfold tailWord_586881
  simp only [CollatzResearch.WordTrace]
  refine ⟨21405308586837843140088497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14270205724558562093392331 21405308586837843140088497)
  ·
    refine ⟨16053981440128382355066373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21405308586837843140088497 16053981440128382355066373)
    ·
      refine ⟨3010121520024071691574945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16053981440128382355066373 3010121520024071691574945)
      ·
        refine ⟨2257591140018053768681209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3010121520024071691574945 2257591140018053768681209)
        ·
          refine ⟨1693193355013540326510907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2257591140018053768681209 1693193355013540326510907)
          ·
            refine ⟨2539790032520310489766361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1693193355013540326510907 2539790032520310489766361)
            ·
              refine ⟨1904842524390232867324771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2539790032520310489766361 1904842524390232867324771)
              ·
                refine ⟨2857263786585349300987157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1904842524390232867324771 2857263786585349300987157)
                ·
                  refine ⟨133934239996188248483773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2857263786585349300987157 133934239996188248483773)
                  ·
                    rfl

theorem cell21_586881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 6].length) (baseStart_586881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_586881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_586881 prefixEnd_586881 := by exact prefixLift 586881
  have htrace : WordTrace (prefixWord ++ tailWord_586881) baseStart_586881 baseEnd_586881 := by
    simpa [prefixWord, tailWord_586881, baseEnd_586881] using wordTrace_append hprefix tailTrace_586881
  have hstable : (prefixWord ++ tailWord_586881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586881).length < 2 ^ (prefixWord ++ tailWord_586881).sum := by decide
  have hdescent : baseEnd_586881 < baseStart_586881 := by decide
  rcases family_descends (prefixWord ++ tailWord_586881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586898 : List Nat := [3, 2, 3, 1, 1, 3, 1, 3, 4]
def baseStart_586898 : Nat := 118140960795 + 586898 * 2 ^ 59
def prefixEnd_586898 : Nat := 4983230072969 + 3 ^ 40 * 586898 * 2
def baseEnd_586898 : Nat := 133938119627799996700405

theorem tailTrace_586898 : CollatzResearch.WordTrace tailWord_586898 prefixEnd_586898 133938119627799996700405 := by
  unfold tailWord_586898
  simp only [CollatzResearch.WordTrace]
  refine ⟨5351482156944063760864337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14270619085184170028971565 5351482156944063760864337)
  ·
    refine ⟨4013611617708047820648253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5351482156944063760864337 4013611617708047820648253)
    ·
      refine ⟨1505104356640517932743095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4013611617708047820648253 1505104356640517932743095)
      ·
        refine ⟨2257656534960776899114643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1505104356640517932743095 2257656534960776899114643)
        ·
          refine ⟨3386484802441165348671965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2257656534960776899114643 3386484802441165348671965)
          ·
            refine ⟨1269931800915437005751987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3386484802441165348671965 1269931800915437005751987)
            ·
              refine ⟨1904897701373155508627981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1269931800915437005751987 1904897701373155508627981)
              ·
                refine ⟨714336638014933315735493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1904897701373155508627981 714336638014933315735493)
                ·
                  refine ⟨133938119627799996700405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 714336638014933315735493 133938119627799996700405)
                  ·
                    rfl

theorem cell21_586898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_586898 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_586898 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_586898 prefixEnd_586898 := by exact prefixLift 586898
  have htrace : WordTrace (prefixWord ++ tailWord_586898) baseStart_586898 baseEnd_586898 := by
    simpa [prefixWord, tailWord_586898, baseEnd_586898] using wordTrace_append hprefix tailTrace_586898
  have hstable : (prefixWord ++ tailWord_586898).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586898).length < 2 ^ (prefixWord ++ tailWord_586898).sum := by decide
  have hdescent : baseEnd_586898 < baseStart_586898 := by decide
  rcases family_descends (prefixWord ++ tailWord_586898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586991 : List Nat := [1, 1, 2, 1, 8, 1, 1, 2, 4]
def baseStart_586991 : Nat := 118140960795 + 586991 * 2 ^ 59
def prefixEnd_586991 : Nat := 4983230072969 + 3 ^ 40 * 586991 * 2
def baseEnd_586991 : Nat := 133959343494852501650215

theorem tailTrace_586991 : CollatzResearch.WordTrace tailWord_586991 prefixEnd_586991 133959343494852501650215 := by
  unfold tailWord_586991
  simp only [CollatzResearch.WordTrace]
  refine ⟨21409320616439331926592827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14272880410959554617728551 21409320616439331926592827)
  ·
    refine ⟨32113980924658997889889241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21409320616439331926592827 32113980924658997889889241)
    ·
      refine ⟨24085485693494248417416931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32113980924658997889889241 24085485693494248417416931)
      ·
        refine ⟨36128228540241372626125397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24085485693494248417416931 36128228540241372626125397)
        ·
          refine ⟨423377678205953585462407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 36128228540241372626125397 423377678205953585462407)
          ·
            refine ⟨635066517308930378193611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 423377678205953585462407 635066517308930378193611)
            ·
              refine ⟨952599775963395567290417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 635066517308930378193611 952599775963395567290417)
              ·
                refine ⟨714449831972546675467813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 952599775963395567290417 714449831972546675467813)
                ·
                  refine ⟨133959343494852501650215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 714449831972546675467813 133959343494852501650215)
                  ·
                    rfl

theorem cell21_586991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 2, 4].length) (baseStart_586991 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_586991 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_586991 prefixEnd_586991 := by exact prefixLift 586991
  have htrace : WordTrace (prefixWord ++ tailWord_586991) baseStart_586991 baseEnd_586991 := by
    simpa [prefixWord, tailWord_586991, baseEnd_586991] using wordTrace_append hprefix tailTrace_586991
  have hstable : (prefixWord ++ tailWord_586991).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586991).length < 2 ^ (prefixWord ++ tailWord_586991).sum := by decide
  have hdescent : baseEnd_586991 < baseStart_586991 := by decide
  rcases family_descends (prefixWord ++ tailWord_586991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587002 : List Nat := [3, 1, 1, 1, 1, 4, 4, 1, 5]
def baseStart_587002 : Nat := 118140960795 + 587002 * 2 ^ 59
def prefixEnd_587002 : Nat := 4983230072969 + 3 ^ 40 * 587002 * 2
def baseEnd_587002 : Nat := 133961853844718926966859

theorem tailTrace_587002 : CollatzResearch.WordTrace tailWord_587002 prefixEnd_587002 133961853844718926966859 := by
  unfold tailWord_587002
  simp only [CollatzResearch.WordTrace]
  refine ⟨5352430454849870201310815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14273147879599653870162173 5352430454849870201310815)
  ·
    refine ⟨8028645682274805301966223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5352430454849870201310815 8028645682274805301966223)
    ·
      refine ⟨12042968523412207952949335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8028645682274805301966223 12042968523412207952949335)
      ·
        refine ⟨18064452785118311929424003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12042968523412207952949335 18064452785118311929424003)
        ·
          refine ⟨27096679177677467894136005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18064452785118311929424003 27096679177677467894136005)
          ·
            refine ⟨5080627345814525230150501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27096679177677467894136005 5080627345814525230150501)
            ·
              refine ⟨952617627340223480653219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5080627345814525230150501 952617627340223480653219)
              ·
                refine ⟨1428926441010335220979829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 952617627340223480653219 1428926441010335220979829)
                ·
                  refine ⟨133961853844718926966859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1428926441010335220979829 133961853844718926966859)
                  ·
                    rfl

theorem cell21_587002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 1, 5].length) (baseStart_587002 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_587002 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_587002 prefixEnd_587002 := by exact prefixLift 587002
  have htrace : WordTrace (prefixWord ++ tailWord_587002) baseStart_587002 baseEnd_587002 := by
    simpa [prefixWord, tailWord_587002, baseEnd_587002] using wordTrace_append hprefix tailTrace_587002
  have hstable : (prefixWord ++ tailWord_587002).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587002).length < 2 ^ (prefixWord ++ tailWord_587002).sum := by decide
  have hdescent : baseEnd_587002 < baseStart_587002 := by decide
  rcases family_descends (prefixWord ++ tailWord_587002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587109 : List Nat := [1, 3, 1, 3, 1, 2, 4, 2, 4]
def baseStart_587109 : Nat := 118140960795 + 587109 * 2 ^ 59
def prefixEnd_587109 : Nat := 4983230072969 + 3 ^ 40 * 587109 * 2
def baseEnd_587109 : Nat := 133986272702510518683307

theorem tailTrace_587109 : CollatzResearch.WordTrace tailWord_587109 prefixEnd_587109 133986272702510518683307 := by
  unfold tailWord_587109
  simp only [CollatzResearch.WordTrace]
  refine ⟨21413624430011838079388381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14275749620007892052925587 21413624430011838079388381)
  ·
    refine ⟨8030109161254439279770643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21413624430011838079388381 8030109161254439279770643)
    ·
      refine ⟨12045163741881658919655965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8030109161254439279770643 12045163741881658919655965)
      ·
        refine ⟨4516936403205622094870987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12045163741881658919655965 4516936403205622094870987)
        ·
          refine ⟨6775404604808433142306481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4516936403205622094870987 6775404604808433142306481)
          ·
            refine ⟨5081553453606324856729861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6775404604808433142306481 5081553453606324856729861)
            ·
              refine ⟨952791272551185910636849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5081553453606324856729861 952791272551185910636849)
              ·
                refine ⟨714593454413389432977637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 952791272551185910636849 714593454413389432977637)
                ·
                  refine ⟨133986272702510518683307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 714593454413389432977637 133986272702510518683307)
                  ·
                    rfl

theorem cell21_587109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 2, 4].length) (baseStart_587109 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_587109 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_587109 prefixEnd_587109 := by exact prefixLift 587109
  have htrace : WordTrace (prefixWord ++ tailWord_587109) baseStart_587109 baseEnd_587109 := by
    simpa [prefixWord, tailWord_587109, baseEnd_587109] using wordTrace_append hprefix tailTrace_587109
  have hstable : (prefixWord ++ tailWord_587109).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587109).length < 2 ^ (prefixWord ++ tailWord_587109).sum := by decide
  have hdescent : baseEnd_587109 < baseStart_587109 := by decide
  rcases family_descends (prefixWord ++ tailWord_587109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587112 : List Nat := [2, 1, 4, 2, 3, 1, 1, 4, 3]
def baseStart_587112 : Nat := 118140960795 + 587112 * 2 ^ 59
def prefixEnd_587112 : Nat := 4983230072969 + 3 ^ 40 * 587112 * 2
def baseEnd_587112 : Nat := 133986957343383180133301

theorem tailTrace_587112 : CollatzResearch.WordTrace tailWord_587112 prefixEnd_587112 133986957343383180133301 := by
  unfold tailWord_587112
  simp only [CollatzResearch.WordTrace]
  refine ⟨10706866924500484795873795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14275822566000646394498393 10706866924500484795873795)
  ·
    refine ⟨16060300386750727193810693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10706866924500484795873795 16060300386750727193810693)
    ·
      refine ⟨3011306322515761348839505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16060300386750727193810693 3011306322515761348839505)
      ·
        refine ⟨2258479741886821011629629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3011306322515761348839505 2258479741886821011629629)
        ·
          refine ⟨846929903207557879361111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2258479741886821011629629 846929903207557879361111)
          ·
            refine ⟨1270394854811336819041667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 846929903207557879361111 1270394854811336819041667)
            ·
              refine ⟨1905592282217005228562501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1270394854811336819041667 1905592282217005228562501)
              ·
                refine ⟨357298552915688480355469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1905592282217005228562501 357298552915688480355469)
                ·
                  refine ⟨133986957343383180133301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 357298552915688480355469 133986957343383180133301)
                  ·
                    rfl

theorem cell21_587112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 4, 3].length) (baseStart_587112 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_587112 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_587112 prefixEnd_587112 := by exact prefixLift 587112
  have htrace : WordTrace (prefixWord ++ tailWord_587112) baseStart_587112 baseEnd_587112 := by
    simpa [prefixWord, tailWord_587112, baseEnd_587112] using wordTrace_append hprefix tailTrace_587112
  have hstable : (prefixWord ++ tailWord_587112).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587112).length < 2 ^ (prefixWord ++ tailWord_587112).sum := by decide
  have hdescent : baseEnd_587112 < baseStart_587112 := by decide
  rcases family_descends (prefixWord ++ tailWord_587112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587140 : List Nat := [2, 3, 2, 1, 1, 4, 3, 5]
def baseStart_587140 : Nat := 118140960795 + 587140 * 2 ^ 59
def prefixEnd_587140 : Nat := 4983230072969 + 3 ^ 40 * 587140 * 2
def baseEnd_587140 : Nat := 44664449108287117888859

theorem tailTrace_587140 : CollatzResearch.WordTrace tailWord_587140 prefixEnd_587140 44664449108287117888859 := by
  unfold tailWord_587140
  simp only [CollatzResearch.WordTrace]
  refine ⟨10707377546449765186883437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14276503395266353582511249 10707377546449765186883437)
  ·
    refine ⟨4015266579918661945081289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10707377546449765186883437 4015266579918661945081289)
    ·
      refine ⟨3011449934938996458810967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4015266579918661945081289 3011449934938996458810967)
      ·
        refine ⟨4517174902408494688216451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3011449934938996458810967 4517174902408494688216451)
        ·
          refine ⟨6775762353612742032324677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4517174902408494688216451 6775762353612742032324677)
          ·
            refine ⟨1270455441302389131060877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6775762353612742032324677 1270455441302389131060877)
            ·
              refine ⟨476420790488395924147829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1270455441302389131060877 476420790488395924147829)
              ·
                refine ⟨44664449108287117888859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 476420790488395924147829 44664449108287117888859)
                ·
                  rfl

theorem cell21_587140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 5].length) (baseStart_587140 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_587140 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_587140 prefixEnd_587140 := by exact prefixLift 587140
  have htrace : WordTrace (prefixWord ++ tailWord_587140) baseStart_587140 baseEnd_587140 := by
    simpa [prefixWord, tailWord_587140, baseEnd_587140] using wordTrace_append hprefix tailTrace_587140
  have hstable : (prefixWord ++ tailWord_587140).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587140).length < 2 ^ (prefixWord ++ tailWord_587140).sum := by decide
  have hdescent : baseEnd_587140 < baseStart_587140 := by decide
  rcases family_descends (prefixWord ++ tailWord_587140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587168 : List Nat := [2, 1, 1, 4, 1, 2, 3, 1, 6]
def baseStart_587168 : Nat := 118140960795 + 587168 * 2 ^ 59
def prefixEnd_587168 : Nat := 4983230072969 + 3 ^ 40 * 587168 * 2
def baseEnd_587168 : Nat := 133999737306339527199853

theorem tailTrace_587168 : CollatzResearch.WordTrace tailWord_587168 prefixEnd_587168 133999737306339527199853 := by
  unfold tailWord_587168
  simp only [CollatzResearch.WordTrace]
  refine ⟨10707888168399045577893079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14277184224532060770524105 10707888168399045577893079)
  ·
    refine ⟨16061832252598568366839619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10707888168399045577893079 16061832252598568366839619)
    ·
      refine ⟨24092748378897852550259429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16061832252598568366839619 24092748378897852550259429)
      ·
        refine ⟨4517390321043347353173643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24092748378897852550259429 4517390321043347353173643)
        ·
          refine ⟨6776085481565021029760465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4517390321043347353173643 6776085481565021029760465)
          ·
            refine ⟨5082064111173765772320349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6776085481565021029760465 5082064111173765772320349)
            ·
              refine ⟨1905774041690162164620131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5082064111173765772320349 1905774041690162164620131)
              ·
                refine ⟨2858661062535243246930197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1905774041690162164620131 2858661062535243246930197)
                ·
                  refine ⟨133999737306339527199853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2858661062535243246930197 133999737306339527199853)
                  ·
                    rfl

theorem cell21_587168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 6].length) (baseStart_587168 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_587168 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_587168 prefixEnd_587168 := by exact prefixLift 587168
  have htrace : WordTrace (prefixWord ++ tailWord_587168) baseStart_587168 baseEnd_587168 := by
    simpa [prefixWord, tailWord_587168, baseEnd_587168] using wordTrace_append hprefix tailTrace_587168
  have hstable : (prefixWord ++ tailWord_587168).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587168).length < 2 ^ (prefixWord ++ tailWord_587168).sum := by decide
  have hdescent : baseEnd_587168 < baseStart_587168 := by decide
  rcases family_descends (prefixWord ++ tailWord_587168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587258 : List Nat := [3, 1, 1, 1, 1, 2, 3, 9]
def baseStart_587258 : Nat := 118140960795 + 587258 * 2 ^ 59
def prefixEnd_587258 : Nat := 4983230072969 + 3 ^ 40 * 587258 * 2
def baseEnd_587258 : Nat := 44673425510839790233223

theorem tailTrace_587258 : CollatzResearch.WordTrace tailWord_587258 prefixEnd_587258 44673425510839790233223 := by
  unfold tailWord_587258
  simp only [CollatzResearch.WordTrace]
  refine ⟨5354764726618009131640607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14279372604314691017708285 5354764726618009131640607)
  ·
    refine ⟨8032147089927013697460911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5354764726618009131640607 8032147089927013697460911)
    ·
      refine ⟨12048220634890520546191367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8032147089927013697460911 12048220634890520546191367)
      ·
        refine ⟨18072330952335780819287051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12048220634890520546191367 18072330952335780819287051)
        ·
          refine ⟨27108496428503671228930577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18072330952335780819287051 27108496428503671228930577)
          ·
            refine ⟨20331372321377753421697933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27108496428503671228930577 20331372321377753421697933)
            ·
              refine ⟨7624264620516657533136725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20331372321377753421697933 7624264620516657533136725)
              ·
                refine ⟨44673425510839790233223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7624264620516657533136725 44673425510839790233223)
                ·
                  rfl

theorem cell21_587258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 9].length) (baseStart_587258 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_587258 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_587258 prefixEnd_587258 := by exact prefixLift 587258
  have htrace : WordTrace (prefixWord ++ tailWord_587258) baseStart_587258 baseEnd_587258 := by
    simpa [prefixWord, tailWord_587258, baseEnd_587258] using wordTrace_append hprefix tailTrace_587258
  have hstable : (prefixWord ++ tailWord_587258).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587258).length < 2 ^ (prefixWord ++ tailWord_587258).sum := by decide
  have hdescent : baseEnd_587258 < baseStart_587258 := by decide
  rcases family_descends (prefixWord ++ tailWord_587258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587275 : List Nat := [1, 1, 1, 1, 9, 8]
def baseStart_587275 : Nat := 118140960795 + 587275 * 2 ^ 59
def prefixEnd_587275 : Nat := 4983230072969 + 3 ^ 40 * 587275 * 2
def baseEnd_587275 : Nat := 4963857635708559959863

theorem tailTrace_587275 : CollatzResearch.WordTrace tailWord_587275 prefixEnd_587275 4963857635708559959863 := by
  unfold tailWord_587275
  simp only [CollatzResearch.WordTrace]
  refine ⟨21419678947410448429931279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14279785964940298953287519 21419678947410448429931279)
  ·
    refine ⟨32129518421115672644896919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21419678947410448429931279 32129518421115672644896919)
    ·
      refine ⟨48194277631673508967345379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32129518421115672644896919 48194277631673508967345379)
      ·
        refine ⟨72291416447510263451018069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48194277631673508967345379 72291416447510263451018069)
        ·
          refine ⟨423582518247130449908309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 72291416447510263451018069 423582518247130449908309)
          ·
            refine ⟨4963857635708559959863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 423582518247130449908309 4963857635708559959863)
            ·
              rfl

theorem cell21_587275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 8].length) (baseStart_587275 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_587275 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_587275 prefixEnd_587275 := by exact prefixLift 587275
  have htrace : WordTrace (prefixWord ++ tailWord_587275) baseStart_587275 baseEnd_587275 := by
    simpa [prefixWord, tailWord_587275, baseEnd_587275] using wordTrace_append hprefix tailTrace_587275
  have hstable : (prefixWord ++ tailWord_587275).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587275).length < 2 ^ (prefixWord ++ tailWord_587275).sum := by decide
  have hdescent : baseEnd_587275 < baseStart_587275 := by decide
  rcases family_descends (prefixWord ++ tailWord_587275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587278 : List Nat := [4, 1, 1, 2, 4, 1, 2, 2, 4]
def baseStart_587278 : Nat := 118140960795 + 587278 * 2 ^ 59
def prefixEnd_587278 : Nat := 4983230072969 + 3 ^ 40 * 587278 * 2
def baseEnd_587278 : Nat := 134024840805003780366295

theorem tailTrace_587278 : CollatzResearch.WordTrace tailWord_587278 prefixEnd_587278 134024840805003780366295 := by
  unfold tailWord_587278
  simp only [CollatzResearch.WordTrace]
  refine ⟨2677473545799947492786311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14279858910933053294860325 2677473545799947492786311)
  ·
    refine ⟨4016210318699921239179467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2677473545799947492786311 4016210318699921239179467)
    ·
      refine ⟨6024315478049881858769201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4016210318699921239179467 6024315478049881858769201)
      ·
        refine ⟨4518236608537411394076901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6024315478049881858769201 4518236608537411394076901)
        ·
          refine ⟨847169364100764636389419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4518236608537411394076901 847169364100764636389419)
          ·
            refine ⟨1270754046151146954584129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 847169364100764636389419 1270754046151146954584129)
            ·
              refine ⟨953065534613360215938097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1270754046151146954584129 953065534613360215938097)
              ·
                refine ⟨714799150960020161953573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 953065534613360215938097 714799150960020161953573)
                ·
                  refine ⟨134024840805003780366295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 714799150960020161953573 134024840805003780366295)
                  ·
                    rfl

theorem cell21_587278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_587278 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_587278 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_587278 prefixEnd_587278 := by exact prefixLift 587278
  have htrace : WordTrace (prefixWord ++ tailWord_587278) baseStart_587278 baseEnd_587278 := by
    simpa [prefixWord, tailWord_587278, baseEnd_587278] using wordTrace_append hprefix tailTrace_587278
  have hstable : (prefixWord ++ tailWord_587278).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587278).length < 2 ^ (prefixWord ++ tailWord_587278).sum := by decide
  have hdescent : baseEnd_587278 < baseStart_587278 := by decide
  rcases family_descends (prefixWord ++ tailWord_587278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587306 : List Nat := [3, 1, 4, 1, 1, 1, 3, 2, 5]
def baseStart_587306 : Nat := 118140960795 + 587306 * 2 ^ 59
def prefixEnd_587306 : Nat := 4983230072969 + 3 ^ 40 * 587306 * 2
def baseEnd_587306 : Nat := 134031230786481953899571

theorem tailTrace_587306 : CollatzResearch.WordTrace tailWord_587306 prefixEnd_587306 134031230786481953899571 := by
  unfold tailWord_587306
  simp only [CollatzResearch.WordTrace]
  refine ⟨5355202402574535181077443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14280539740198760482873181 5355202402574535181077443)
  ·
    refine ⟨8032803603861802771616165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5355202402574535181077443 8032803603861802771616165)
    ·
      refine ⟨1506150675724088019678031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8032803603861802771616165 1506150675724088019678031)
      ·
        refine ⟨2259226013586132029517047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1506150675724088019678031 2259226013586132029517047)
        ·
          refine ⟨3388839020379198044275571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2259226013586132029517047 3388839020379198044275571)
          ·
            refine ⟨5083258530568797066413357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3388839020379198044275571 5083258530568797066413357)
            ·
              refine ⟨1906221948963298899905009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5083258530568797066413357 1906221948963298899905009)
              ·
                refine ⟨1429666461722474174928757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1906221948963298899905009 1429666461722474174928757)
                ·
                  refine ⟨134031230786481953899571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1429666461722474174928757 134031230786481953899571)
                  ·
                    rfl

theorem cell21_587306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 2, 5].length) (baseStart_587306 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_587306 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_587306 prefixEnd_587306 := by exact prefixLift 587306
  have htrace : WordTrace (prefixWord ++ tailWord_587306) baseStart_587306 baseEnd_587306 := by
    simpa [prefixWord, tailWord_587306, baseEnd_587306] using wordTrace_append hprefix tailTrace_587306
  have hstable : (prefixWord ++ tailWord_587306).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587306).length < 2 ^ (prefixWord ++ tailWord_587306).sum := by decide
  have hdescent : baseEnd_587306 < baseStart_587306 := by decide
  rcases family_descends (prefixWord ++ tailWord_587306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587368 : List Nat := [2, 1, 4, 3, 1, 1, 4, 5]
def baseStart_587368 : Nat := 118140960795 + 587368 * 2 ^ 59
def prefixEnd_587368 : Nat := 4983230072969 + 3 ^ 40 * 587368 * 2
def baseEnd_587368 : Nat := 44681793343727874622037

theorem tailTrace_587368 : CollatzResearch.WordTrace tailWord_587368 prefixEnd_587368 44681793343727874622037 := by
  unfold tailWord_587368
  simp only [CollatzResearch.WordTrace]
  refine ⟨10711535468036762656533379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14282047290715683542044505 10711535468036762656533379)
  ·
    refine ⟨16067303202055143984800069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10711535468036762656533379 16067303202055143984800069)
    ·
      refine ⟨3012619350385339497150013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16067303202055143984800069 3012619350385339497150013)
      ·
        refine ⟨1129732256394502311431255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3012619350385339497150013 1129732256394502311431255)
        ·
          refine ⟨1694598384591753467146883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1129732256394502311431255 1694598384591753467146883)
          ·
            refine ⟨2541897576887630200720325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1694598384591753467146883 2541897576887630200720325)
            ·
              refine ⟨476605795666430662635061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2541897576887630200720325 476605795666430662635061)
              ·
                refine ⟨44681793343727874622037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 476605795666430662635061 44681793343727874622037)
                ·
                  rfl

theorem cell21_587368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 5].length) (baseStart_587368 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_587368 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_587368 prefixEnd_587368 := by exact prefixLift 587368
  have htrace : WordTrace (prefixWord ++ tailWord_587368) baseStart_587368 baseEnd_587368 := by
    simpa [prefixWord, tailWord_587368, baseEnd_587368] using wordTrace_append hprefix tailTrace_587368
  have hstable : (prefixWord ++ tailWord_587368).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587368).length < 2 ^ (prefixWord ++ tailWord_587368).sum := by decide
  have hdescent : baseEnd_587368 < baseStart_587368 := by decide
  rcases family_descends (prefixWord ++ tailWord_587368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587478 : List Nat := [5, 2, 1, 3, 1, 1, 3, 5]
def baseStart_587478 : Nat := 118140960795 + 587478 * 2 ^ 59
def prefixEnd_587478 : Nat := 4983230072969 + 3 ^ 40 * 587478 * 2
def baseEnd_587478 : Nat := 44690161176615959010851

theorem tailTrace_587478 : CollatzResearch.WordTrace tailWord_587478 prefixEnd_587478 44690161176615959010851 := by
  unfold tailWord_587478
  simp only [CollatzResearch.WordTrace]
  refine ⟨1339192685354688381223193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14284721977116676066380725 1339192685354688381223193)
  ·
    refine ⟨1004394514016016285917395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1339192685354688381223193 1004394514016016285917395)
    ·
      refine ⟨1506591771024024428876093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1004394514016016285917395 1506591771024024428876093)
      ·
        refine ⟨564971914134009160828535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1506591771024024428876093 564971914134009160828535)
        ·
          refine ⟨847457871201013741242803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 564971914134009160828535 847457871201013741242803)
          ·
            refine ⟨1271186806801520611864205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 847457871201013741242803 1271186806801520611864205)
            ·
              refine ⟨476695052550570229449077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1271186806801520611864205 476695052550570229449077)
              ·
                refine ⟨44690161176615959010851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 476695052550570229449077 44690161176615959010851)
                ·
                  rfl

theorem cell21_587478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_587478 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_587478 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_587478 prefixEnd_587478 := by exact prefixLift 587478
  have htrace : WordTrace (prefixWord ++ tailWord_587478) baseStart_587478 baseEnd_587478 := by
    simpa [prefixWord, tailWord_587478, baseEnd_587478] using wordTrace_append hprefix tailTrace_587478
  have hstable : (prefixWord ++ tailWord_587478).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587478).length < 2 ^ (prefixWord ++ tailWord_587478).sum := by decide
  have hdescent : baseEnd_587478 < baseStart_587478 := by decide
  rcases family_descends (prefixWord ++ tailWord_587478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587582 : List Nat := [4, 2, 1, 2, 2, 1, 4, 1, 4]
def baseStart_587582 : Nat := 118140960795 + 587582 * 2 ^ 59
def prefixEnd_587582 : Nat := 4983230072969 + 3 ^ 40 * 587582 * 2
def baseEnd_587582 : Nat := 134094217746766807299007

theorem tailTrace_587582 : CollatzResearch.WordTrace tailWord_587582 prefixEnd_587582 134094217746766807299007 := by
  unfold tailWord_587582
  simp only [CollatzResearch.WordTrace]
  refine ⟨2678859519662279982669625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14287250771532159907571333 2678859519662279982669625)
  ·
    refine ⟨2009144639746709987002219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2678859519662279982669625 2009144639746709987002219)
    ·
      refine ⟨3013716959620064980503329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2009144639746709987002219 3013716959620064980503329)
      ·
        refine ⟨2260287719715048735377497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3013716959620064980503329 2260287719715048735377497)
        ·
          refine ⟨1695215789786286551533123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2260287719715048735377497 1695215789786286551533123)
          ·
            refine ⟨2542823684679429827299685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1695215789786286551533123 2542823684679429827299685)
            ·
              refine ⟨476779440877393092618691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2542823684679429827299685 476779440877393092618691)
              ·
                refine ⟨715169161316089638928037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 476779440877393092618691 715169161316089638928037)
                ·
                  refine ⟨134094217746766807299007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 715169161316089638928037 134094217746766807299007)
                  ·
                    rfl

theorem cell21_587582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_587582 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_587582 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_587582 prefixEnd_587582 := by exact prefixLift 587582
  have htrace : WordTrace (prefixWord ++ tailWord_587582) baseStart_587582 baseEnd_587582 := by
    simpa [prefixWord, tailWord_587582, baseEnd_587582] using wordTrace_append hprefix tailTrace_587582
  have hstable : (prefixWord ++ tailWord_587582).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587582).length < 2 ^ (prefixWord ++ tailWord_587582).sum := by decide
  have hdescent : baseEnd_587582 < baseStart_587582 := by decide
  rcases family_descends (prefixWord ++ tailWord_587582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587610 : List Nat := [3, 1, 1, 2, 1, 3, 2, 5, 3]
def baseStart_587610 : Nat := 118140960795 + 587610 * 2 ^ 59
def prefixEnd_587610 : Nat := 4983230072969 + 3 ^ 40 * 587610 * 2
def baseEnd_587610 : Nat := 134100607728244980832283

theorem tailTrace_587610 : CollatzResearch.WordTrace tailWord_587610 prefixEnd_587610 134100607728244980832283 := by
  unfold tailWord_587610
  simp only [CollatzResearch.WordTrace]
  refine ⟨5357974350299200160844071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14287931600797867095584189 5357974350299200160844071)
  ·
    refine ⟨8036961525448800241266107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5357974350299200160844071 8036961525448800241266107)
    ·
      refine ⟨12055442288173200361899161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8036961525448800241266107 12055442288173200361899161)
      ·
        refine ⟨9041581716129900271424371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12055442288173200361899161 9041581716129900271424371)
        ·
          refine ⟨13562372574194850407136557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9041581716129900271424371 13562372574194850407136557)
          ·
            refine ⟨5085889715323068902676209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13562372574194850407136557 5085889715323068902676209)
            ·
              refine ⟨3814417286492301677007157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5085889715323068902676209 3814417286492301677007157)
              ·
                refine ⟨357601620608653282219421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3814417286492301677007157 357601620608653282219421)
                ·
                  refine ⟨134100607728244980832283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 357601620608653282219421 134100607728244980832283)
                  ·
                    rfl

theorem cell21_587610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 5, 3].length) (baseStart_587610 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_587610 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_587610 prefixEnd_587610 := by exact prefixLift 587610
  have htrace : WordTrace (prefixWord ++ tailWord_587610) baseStart_587610 baseEnd_587610 := by
    simpa [prefixWord, tailWord_587610, baseEnd_587610] using wordTrace_append hprefix tailTrace_587610
  have hstable : (prefixWord ++ tailWord_587610).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587610).length < 2 ^ (prefixWord ++ tailWord_587610).sum := by decide
  have hdescent : baseEnd_587610 < baseStart_587610 := by decide
  rcases family_descends (prefixWord ++ tailWord_587610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587728 : List Nat := [2, 1, 1, 1, 1, 2, 4, 2, 7]
def baseStart_587728 : Nat := 118140960795 + 587728 * 2 ^ 59
def prefixEnd_587728 : Nat := 4983230072969 + 3 ^ 40 * 587728 * 2
def baseEnd_587728 : Nat := 134127536935902997865375

theorem tailTrace_587728 : CollatzResearch.WordTrace tailWord_587728 prefixEnd_587728 134127536935902997865375 := by
  unfold tailWord_587728
  simp only [CollatzResearch.WordTrace]
  refine ⟨10718100607384653398085919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14290800809846204530781225 10718100607384653398085919)
  ·
    refine ⟨16077150911076980097128879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10718100607384653398085919 16077150911076980097128879)
    ·
      refine ⟨24115726366615470145693319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16077150911076980097128879 24115726366615470145693319)
      ·
        refine ⟨36173589549923205218539979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24115726366615470145693319 36173589549923205218539979)
        ·
          refine ⟨54260384324884807827809969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36173589549923205218539979 54260384324884807827809969)
          ·
            refine ⟨40695288243663605870857477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54260384324884807827809969 40695288243663605870857477)
            ·
              refine ⟨7630366545686926100785777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40695288243663605870857477 7630366545686926100785777)
              ·
                refine ⟨5722774909265194575589333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7630366545686926100785777 5722774909265194575589333)
                ·
                  refine ⟨134127536935902997865375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5722774909265194575589333 134127536935902997865375)
                  ·
                    rfl

theorem cell21_587728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 7].length) (baseStart_587728 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_587728 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_587728 prefixEnd_587728 := by exact prefixLift 587728
  have htrace : WordTrace (prefixWord ++ tailWord_587728) baseStart_587728 baseEnd_587728 := by
    simpa [prefixWord, tailWord_587728, baseEnd_587728] using wordTrace_append hprefix tailTrace_587728
  have hstable : (prefixWord ++ tailWord_587728).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587728).length < 2 ^ (prefixWord ++ tailWord_587728).sum := by decide
  have hdescent : baseEnd_587728 < baseStart_587728 := by decide
  rcases family_descends (prefixWord ++ tailWord_587728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587745 : List Nat := [1, 2, 3, 1, 2, 1, 5, 1, 5]
def baseStart_587745 : Nat := 118140960795 + 587745 * 2 ^ 59
def prefixEnd_587745 : Nat := 4983230072969 + 3 ^ 40 * 587745 * 2
def baseEnd_587745 : Nat := 134131416567514746082007

theorem tailTrace_587745 : CollatzResearch.WordTrace tailWord_587745 prefixEnd_587745 134131416567514746082007 := by
  unfold tailWord_587745
  simp only [CollatzResearch.WordTrace]
  refine ⟨21436821255707718699540689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14291214170471812466360459 21436821255707718699540689)
  ·
    refine ⟨16077615941780789024655517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21436821255707718699540689 16077615941780789024655517)
    ·
      refine ⟨6029105978167795884245819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16077615941780789024655517 6029105978167795884245819)
      ·
        refine ⟨9043658967251693826368729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6029105978167795884245819 9043658967251693826368729)
        ·
          refine ⟨6782744225438770369776547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9043658967251693826368729 6782744225438770369776547)
          ·
            refine ⟨10174116338158155554664821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6782744225438770369776547 10174116338158155554664821)
            ·
              refine ⟨953823406702327083249827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10174116338158155554664821 953823406702327083249827)
              ·
                refine ⟨1430735110053490624874741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 953823406702327083249827 1430735110053490624874741)
                ·
                  refine ⟨134131416567514746082007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1430735110053490624874741 134131416567514746082007)
                  ·
                    rfl

theorem cell21_587745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 1, 5].length) (baseStart_587745 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_587745 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_587745 prefixEnd_587745 := by exact prefixLift 587745
  have htrace : WordTrace (prefixWord ++ tailWord_587745) baseStart_587745 baseEnd_587745 := by
    simpa [prefixWord, tailWord_587745, baseEnd_587745] using wordTrace_append hprefix tailTrace_587745
  have hstable : (prefixWord ++ tailWord_587745).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587745).length < 2 ^ (prefixWord ++ tailWord_587745).sum := by decide
  have hdescent : baseEnd_587745 < baseStart_587745 := by decide
  rcases family_descends (prefixWord ++ tailWord_587745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587751 : List Nat := [1, 1, 5, 2, 4, 1, 2, 1, 4]
def baseStart_587751 : Nat := 118140960795 + 587751 * 2 ^ 59
def prefixEnd_587751 : Nat := 4983230072969 + 3 ^ 40 * 587751 * 2
def baseEnd_587751 : Nat := 134132785849260068981995

theorem tailTrace_587751 : CollatzResearch.WordTrace tailWord_587751 prefixEnd_587751 134132785849260068981995 := by
  unfold tailWord_587751
  simp only [CollatzResearch.WordTrace]
  refine ⟨21437040093685981724259107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14291360062457321149506071 21437040093685981724259107)
  ·
    refine ⟨32155560140528972586388661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21437040093685981724259107 32155560140528972586388661)
    ·
      refine ⟨3014583763174591179973937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32155560140528972586388661 3014583763174591179973937)
      ·
        refine ⟨2260937822380943384980453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3014583763174591179973937 2260937822380943384980453)
        ·
          refine ⟨423925841696426884683835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2260937822380943384980453 423925841696426884683835)
          ·
            refine ⟨635888762544640327025753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 423925841696426884683835 635888762544640327025753)
            ·
              refine ⟨476916571908480245269315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 635888762544640327025753 476916571908480245269315)
              ·
                refine ⟨715374857862720367903973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 476916571908480245269315 715374857862720367903973)
                ·
                  refine ⟨134132785849260068981995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 715374857862720367903973 134132785849260068981995)
                  ·
                    rfl

theorem cell21_587751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 1, 4].length) (baseStart_587751 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_587751 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_587751 prefixEnd_587751 := by exact prefixLift 587751
  have htrace : WordTrace (prefixWord ++ tailWord_587751) baseStart_587751 baseEnd_587751 := by
    simpa [prefixWord, tailWord_587751, baseEnd_587751] using wordTrace_append hprefix tailTrace_587751
  have hstable : (prefixWord ++ tailWord_587751).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587751).length < 2 ^ (prefixWord ++ tailWord_587751).sum := by decide
  have hdescent : baseEnd_587751 < baseStart_587751 := by decide
  rcases family_descends (prefixWord ++ tailWord_587751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587782 : List Nat := [6, 2, 1, 2, 2, 8]
def baseStart_587782 : Nat := 118140960795 + 587782 * 2 ^ 59
def prefixEnd_587782 : Nat := 4983230072969 + 3 ^ 40 * 587782 * 2
def baseEnd_587782 : Nat := 4968142980430033480195

theorem tailTrace_587782 : CollatzResearch.WordTrace tailWord_587782 prefixEnd_587782 4968142980430033480195 := by
  unfold tailWord_587782
  simp only [CollatzResearch.WordTrace]
  refine ⟨669942836142927313082425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14292113837715782679091733 669942836142927313082425)
  ·
    refine ⟨502457127107195484811819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 669942836142927313082425 502457127107195484811819)
    ·
      refine ⟨753685690660793227217729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 502457127107195484811819 753685690660793227217729)
      ·
        refine ⟨565264267995594920413297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 753685690660793227217729 565264267995594920413297)
        ·
          refine ⟨423948200996696190309973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 565264267995594920413297 423948200996696190309973)
          ·
            refine ⟨4968142980430033480195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 423948200996696190309973 4968142980430033480195)
            ·
              rfl

theorem cell21_587782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 8].length) (baseStart_587782 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_587782 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_587782 prefixEnd_587782 := by exact prefixLift 587782
  have htrace : WordTrace (prefixWord ++ tailWord_587782) baseStart_587782 baseEnd_587782 := by
    simpa [prefixWord, tailWord_587782, baseEnd_587782] using wordTrace_append hprefix tailTrace_587782
  have hstable : (prefixWord ++ tailWord_587782).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587782).length < 2 ^ (prefixWord ++ tailWord_587782).sum := by decide
  have hdescent : baseEnd_587782 < baseStart_587782 := by decide
  rcases family_descends (prefixWord ++ tailWord_587782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587849 : List Nat := [1, 2, 1, 1, 2, 2, 12]
def baseStart_587849 : Nat := 118140960795 + 587849 * 2 ^ 59
def prefixEnd_587849 : Nat := 4983230072969 + 3 ^ 40 * 587849 * 2
def baseEnd_587849 : Nat := 14906127864937075149829

theorem tailTrace_587849 : CollatzResearch.WordTrace tailWord_587849 prefixEnd_587849 14906127864937075149829 := by
  unfold tailWord_587849
  simp only [CollatzResearch.WordTrace]
  refine ⟨21440614447330944461326601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14293742964887296307551067 21440614447330944461326601)
  ·
    refine ⟨16080460835498208345994951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21440614447330944461326601 16080460835498208345994951)
    ·
      refine ⟨24120691253247312518992427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16080460835498208345994951 24120691253247312518992427)
      ·
        refine ⟨36181036879870968778488641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24120691253247312518992427 36181036879870968778488641)
        ·
          refine ⟨27135777659903226583866481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36181036879870968778488641 27135777659903226583866481)
          ·
            refine ⟨20351833244927419937899861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27135777659903226583866481 20351833244927419937899861)
            ·
              refine ⟨14906127864937075149829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 20351833244927419937899861 14906127864937075149829)
              ·
                rfl

theorem cell21_587849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 12].length) (baseStart_587849 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_587849 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_587849 prefixEnd_587849 := by exact prefixLift 587849
  have htrace : WordTrace (prefixWord ++ tailWord_587849) baseStart_587849 baseEnd_587849 := by
    simpa [prefixWord, tailWord_587849, baseEnd_587849] using wordTrace_append hprefix tailTrace_587849
  have hstable : (prefixWord ++ tailWord_587849).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587849).length < 2 ^ (prefixWord ++ tailWord_587849).sum := by decide
  have hdescent : baseEnd_587849 < baseStart_587849 := by decide
  rcases family_descends (prefixWord ++ tailWord_587849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587852 : List Nat := [2, 2, 1, 3, 1, 1, 5, 2, 4]
def baseStart_587852 : Nat := 118140960795 + 587852 * 2 ^ 59
def prefixEnd_587852 : Nat := 4983230072969 + 3 ^ 40 * 587852 * 2
def baseEnd_587852 : Nat := 134155835425306337798455

theorem tailTrace_587852 : CollatzResearch.WordTrace tailWord_587852 prefixEnd_587852 134155835425306337798455 := by
  unfold tailWord_587852
  simp only [CollatzResearch.WordTrace]
  refine ⟨10720361933160037986842905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14293815910880050649123873 10720361933160037986842905)
  ·
    refine ⟨8040271449870028490132179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10720361933160037986842905 8040271449870028490132179)
    ·
      refine ⟨12060407174805042735198269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8040271449870028490132179 12060407174805042735198269)
      ·
        refine ⟨4522652690551891025699351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12060407174805042735198269 4522652690551891025699351)
        ·
          refine ⟨6783979035827836538549027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4522652690551891025699351 6783979035827836538549027)
          ·
            refine ⟨10175968553741754807823541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6783979035827836538549027 10175968553741754807823541)
            ·
              refine ⟨953997051913289513233457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10175968553741754807823541 953997051913289513233457)
              ·
                refine ⟨715497788934967134925093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 953997051913289513233457 715497788934967134925093)
                ·
                  refine ⟨134155835425306337798455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 715497788934967134925093 134155835425306337798455)
                  ·
                    rfl

theorem cell21_587852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 2, 4].length) (baseStart_587852 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_587852 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_587852 prefixEnd_587852 := by exact prefixLift 587852
  have htrace : WordTrace (prefixWord ++ tailWord_587852) baseStart_587852 baseEnd_587852 := by
    simpa [prefixWord, tailWord_587852, baseEnd_587852] using wordTrace_append hprefix tailTrace_587852
  have hstable : (prefixWord ++ tailWord_587852).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587852).length < 2 ^ (prefixWord ++ tailWord_587852).sum := by decide
  have hdescent : baseEnd_587852 < baseStart_587852 := by decide
  rcases family_descends (prefixWord ++ tailWord_587852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587911 : List Nat := [1, 1, 4, 2, 1, 1, 4, 1, 6]
def baseStart_587911 : Nat := 118140960795 + 587911 * 2 ^ 59
def prefixEnd_587911 : Nat := 4983230072969 + 3 ^ 40 * 587911 * 2
def baseEnd_587911 : Nat := 134169300029135346315001

theorem tailTrace_587911 : CollatzResearch.WordTrace tailWord_587911 prefixEnd_587911 134169300029135346315001 := by
  unfold tailWord_587911
  simp only [CollatzResearch.WordTrace]
  refine ⟨21442875773106329050083587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14295250515404219366722391 21442875773106329050083587)
  ·
    refine ⟨32164313659659493575125381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21442875773106329050083587 32164313659659493575125381)
    ·
      refine ⟨6030808811186155045336009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32164313659659493575125381 6030808811186155045336009)
      ·
        refine ⟨4523106608389616284002007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6030808811186155045336009 4523106608389616284002007)
        ·
          refine ⟨6784659912584424426003011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4523106608389616284002007 6784659912584424426003011)
          ·
            refine ⟨10176989868876636639004517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6784659912584424426003011 10176989868876636639004517)
            ·
              refine ⟨1908185600414369369813347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10176989868876636639004517 1908185600414369369813347)
              ·
                refine ⟨2862278400621554054720021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1908185600414369369813347 2862278400621554054720021)
                ·
                  refine ⟨134169300029135346315001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2862278400621554054720021 134169300029135346315001)
                  ·
                    rfl

theorem cell21_587911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 6].length) (baseStart_587911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_587911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_587911 prefixEnd_587911 := by exact prefixLift 587911
  have htrace : WordTrace (prefixWord ++ tailWord_587911) baseStart_587911 baseEnd_587911 := by
    simpa [prefixWord, tailWord_587911, baseEnd_587911] using wordTrace_append hprefix tailTrace_587911
  have hstable : (prefixWord ++ tailWord_587911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587911).length < 2 ^ (prefixWord ++ tailWord_587911).sum := by decide
  have hdescent : baseEnd_587911 < baseStart_587911 := by decide
  rcases family_descends (prefixWord ++ tailWord_587911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587914 : List Nat := [3, 1, 2, 3, 1, 4, 1, 1, 5]
def baseStart_587914 : Nat := 118140960795 + 587914 * 2 ^ 59
def prefixEnd_587914 : Nat := 4983230072969 + 3 ^ 40 * 587914 * 2
def baseEnd_587914 : Nat := 134169984670008007764995

theorem tailTrace_587914 : CollatzResearch.WordTrace tailWord_587914 prefixEnd_587914 134169984670008007764995 := by
  unfold tailWord_587914
  simp only [CollatzResearch.WordTrace]
  refine ⟨5360746298023865140610699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14295323461396973708295197 5360746298023865140610699)
  ·
    refine ⟨8041119447035797710916049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5360746298023865140610699 8041119447035797710916049)
    ·
      refine ⟨6030839585276848283187037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8041119447035797710916049 6030839585276848283187037)
      ·
        refine ⟨2261564844478818106195139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6030839585276848283187037 2261564844478818106195139)
        ·
          refine ⟨3392347266718227159292709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2261564844478818106195139 3392347266718227159292709)
          ·
            refine ⟨636065112509667592367383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3392347266718227159292709 636065112509667592367383)
            ·
              refine ⟨954097668764501388551075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 636065112509667592367383 954097668764501388551075)
              ·
                refine ⟨1431146503146752082826613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 954097668764501388551075 1431146503146752082826613)
                ·
                  refine ⟨134169984670008007764995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1431146503146752082826613 134169984670008007764995)
                  ·
                    rfl

theorem cell21_587914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 1, 5].length) (baseStart_587914 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_587914 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_587914 prefixEnd_587914 := by exact prefixLift 587914
  have htrace : WordTrace (prefixWord ++ tailWord_587914) baseStart_587914 baseEnd_587914 := by
    simpa [prefixWord, tailWord_587914, baseEnd_587914] using wordTrace_append hprefix tailTrace_587914
  have hstable : (prefixWord ++ tailWord_587914).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587914).length < 2 ^ (prefixWord ++ tailWord_587914).sum := by decide
  have hdescent : baseEnd_587914 < baseStart_587914 := by decide
  rcases family_descends (prefixWord ++ tailWord_587914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587990 : List Nat := [5, 2, 1, 2, 1, 1, 1, 1, 7]
def baseStart_587990 : Nat := 118140960795 + 587990 * 2 ^ 59
def prefixEnd_587990 : Nat := 4983230072969 + 3 ^ 40 * 587990 * 2
def baseEnd_587990 : Nat := 134187328905448764498173

theorem tailTrace_587990 : CollatzResearch.WordTrace tailWord_587990 prefixEnd_587990 134187328905448764498173 := by
  unfold tailWord_587990
  simp only [CollatzResearch.WordTrace]
  refine ⟨1340359821238757846388089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14297171426546750361472949 1340359821238757846388089)
  ·
    refine ⟨1005269865929068384791067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1340359821238757846388089 1005269865929068384791067)
    ·
      refine ⟨1507904798893602577186601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1005269865929068384791067 1507904798893602577186601)
      ·
        refine ⟨1130928599170201932889951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1507904798893602577186601 1130928599170201932889951)
        ·
          refine ⟨1696392898755302899334927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1130928599170201932889951 1696392898755302899334927)
          ·
            refine ⟨2544589348132954349002391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1696392898755302899334927 2544589348132954349002391)
            ·
              refine ⟨3816884022199431523503587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2544589348132954349002391 3816884022199431523503587)
              ·
                refine ⟨5725326033299147285255381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3816884022199431523503587 5725326033299147285255381)
                ·
                  refine ⟨134187328905448764498173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5725326033299147285255381 134187328905448764498173)
                  ·
                    rfl

theorem cell21_587990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_587990 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_587990 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_587990 prefixEnd_587990 := by exact prefixLift 587990
  have htrace : WordTrace (prefixWord ++ tailWord_587990) baseStart_587990 baseEnd_587990 := by
    simpa [prefixWord, tailWord_587990, baseEnd_587990] using wordTrace_append hprefix tailTrace_587990
  have hstable : (prefixWord ++ tailWord_587990).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587990).length < 2 ^ (prefixWord ++ tailWord_587990).sum := by decide
  have hdescent : baseEnd_587990 < baseStart_587990 := by decide
  rcases family_descends (prefixWord ++ tailWord_587990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588007 : List Nat := [1, 1, 5, 3, 1, 2, 2, 3, 3]
def baseStart_588007 : Nat := 118140960795 + 588007 * 2 ^ 59
def prefixEnd_588007 : Nat := 4983230072969 + 3 ^ 40 * 588007 * 2
def baseEnd_588007 : Nat := 134191208537060512714805

theorem tailTrace_588007 : CollatzResearch.WordTrace tailWord_588007 prefixEnd_588007 134191208537060512714805 := by
  unfold tailWord_588007
  simp only [CollatzResearch.WordTrace]
  refine ⟨21446377180758537445578275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14297584787172358297052183 21446377180758537445578275)
  ·
    refine ⟨32169565771137806168367413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21446377180758537445578275 32169565771137806168367413)
    ·
      refine ⟨3015896791044169328284445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32169565771137806168367413 3015896791044169328284445)
      ·
        refine ⟨1130961296641563498106667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3015896791044169328284445 1130961296641563498106667)
        ·
          refine ⟨1696441944962345247160001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1130961296641563498106667 1696441944962345247160001)
          ·
            refine ⟨1272331458721758935370001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1696441944962345247160001 1272331458721758935370001)
            ·
              refine ⟨954248594041319201527501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1272331458721758935370001 954248594041319201527501)
              ·
                refine ⟨357843222765494700572813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 954248594041319201527501 357843222765494700572813)
                ·
                  refine ⟨134191208537060512714805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 357843222765494700572813 134191208537060512714805)
                  ·
                    rfl

theorem cell21_588007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 3, 3].length) (baseStart_588007 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_588007 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_588007 prefixEnd_588007 := by exact prefixLift 588007
  have htrace : WordTrace (prefixWord ++ tailWord_588007) baseStart_588007 baseEnd_588007 := by
    simpa [prefixWord, tailWord_588007, baseEnd_588007] using wordTrace_append hprefix tailTrace_588007
  have hstable : (prefixWord ++ tailWord_588007).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588007).length < 2 ^ (prefixWord ++ tailWord_588007).sum := by decide
  have hdescent : baseEnd_588007 < baseStart_588007 := by decide
  rcases family_descends (prefixWord ++ tailWord_588007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588018 : List Nat := [3, 2, 1, 3, 2, 2, 8]
def baseStart_588018 : Nat := 118140960795 + 588018 * 2 ^ 59
def prefixEnd_588018 : Nat := 4983230072969 + 3 ^ 40 * 588018 * 2
def baseEnd_588018 : Nat := 14910413209658548670161

theorem tailTrace_588018 : CollatzResearch.WordTrace tailWord_588018 prefixEnd_588018 14910413209658548670161 := by
  unfold tailWord_588018
  simp only [CollatzResearch.WordTrace]
  refine ⟨5361694595929671581057177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14297852255812457549485805 5361694595929671581057177)
  ·
    refine ⟨4021270946947253685792883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5361694595929671581057177 4021270946947253685792883)
    ·
      refine ⟨6031906420420880528689325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4021270946947253685792883 6031906420420880528689325)
      ·
        refine ⟨2261964907657830198258497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6031906420420880528689325 2261964907657830198258497)
        ·
          refine ⟨1696473680743372648693873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2261964907657830198258497 1696473680743372648693873)
          ·
            refine ⟨1272355260557529486520405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1696473680743372648693873 1272355260557529486520405)
            ·
              refine ⟨14910413209658548670161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1272355260557529486520405 14910413209658548670161)
              ·
                rfl

theorem cell21_588018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 8].length) (baseStart_588018 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_588018 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_588018 prefixEnd_588018 := by exact prefixLift 588018
  have htrace : WordTrace (prefixWord ++ tailWord_588018) baseStart_588018 baseEnd_588018 := by
    simpa [prefixWord, tailWord_588018, baseEnd_588018] using wordTrace_append hprefix tailTrace_588018
  have hstable : (prefixWord ++ tailWord_588018).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588018).length < 2 ^ (prefixWord ++ tailWord_588018).sum := by decide
  have hdescent : baseEnd_588018 < baseStart_588018 := by decide
  rcases family_descends (prefixWord ++ tailWord_588018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588032 : List Nat := [2, 1, 1, 2, 1, 1, 5, 3, 5]
def baseStart_588032 : Nat := 118140960795 + 588032 * 2 ^ 59
def prefixEnd_588032 : Nat := 4983230072969 + 3 ^ 40 * 588032 * 2
def baseEnd_588032 : Nat := 134196913877666024798087

theorem tailTrace_588032 : CollatzResearch.WordTrace tailWord_588032 prefixEnd_588032 134196913877666024798087 := by
  unfold tailWord_588032
  simp only [CollatzResearch.WordTrace]
  refine ⟨10723644502833983357619175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14298192670445311143492233 10723644502833983357619175)
  ·
    refine ⟨16085466754250975036428763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10723644502833983357619175 16085466754250975036428763)
    ·
      refine ⟨24128200131376462554643145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16085466754250975036428763 24128200131376462554643145)
      ·
        refine ⟨18096150098532346915982359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24128200131376462554643145 18096150098532346915982359)
        ·
          refine ⟨27144225147798520373973539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18096150098532346915982359 27144225147798520373973539)
          ·
            refine ⟨40716337721697780560960309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27144225147798520373973539 40716337721697780560960309)
            ·
              refine ⟨3817156661409166927590029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40716337721697780560960309 3817156661409166927590029)
              ·
                refine ⟨1431433748028437597846261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3817156661409166927590029 1431433748028437597846261)
                ·
                  refine ⟨134196913877666024798087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1431433748028437597846261 134196913877666024798087)
                  ·
                    rfl

theorem cell21_588032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3, 5].length) (baseStart_588032 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_588032 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_588032 prefixEnd_588032 := by exact prefixLift 588032
  have htrace : WordTrace (prefixWord ++ tailWord_588032) baseStart_588032 baseEnd_588032 := by
    simpa [prefixWord, tailWord_588032, baseEnd_588032] using wordTrace_append hprefix tailTrace_588032
  have hstable : (prefixWord ++ tailWord_588032).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588032).length < 2 ^ (prefixWord ++ tailWord_588032).sum := by decide
  have hdescent : baseEnd_588032 < baseStart_588032 := by decide
  rcases family_descends (prefixWord ++ tailWord_588032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588063 : List Nat := [1, 1, 2, 4, 3, 1, 1, 2, 6]
def baseStart_588063 : Nat := 118140960795 + 588063 * 2 ^ 59
def prefixEnd_588063 : Nat := 4983230072969 + 3 ^ 40 * 588063 * 2
def baseEnd_588063 : Nat := 134203988500016859781357

theorem tailTrace_588063 : CollatzResearch.WordTrace tailWord_588063 prefixEnd_588063 134203988500016859781357 := by
  unfold tailWord_588063
  simp only [CollatzResearch.WordTrace]
  refine ⟨21448419668555659009616843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14298946445703772673077895 21448419668555659009616843)
  ·
    refine ⟨32172629502833488514425265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21448419668555659009616843 32172629502833488514425265)
    ·
      refine ⟨24129472127125116385818949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32172629502833488514425265 24129472127125116385818949)
      ·
        refine ⟨4524276023835959322341053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24129472127125116385818949 4524276023835959322341053)
        ·
          refine ⟨1696603508938484745877895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4524276023835959322341053 1696603508938484745877895)
          ·
            refine ⟨2544905263407727118816843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1696603508938484745877895 2544905263407727118816843)
            ·
              refine ⟨3817357895111590678225265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2544905263407727118816843 3817357895111590678225265)
              ·
                refine ⟨2863018421333693008668949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3817357895111590678225265 2863018421333693008668949)
                ·
                  refine ⟨134203988500016859781357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2863018421333693008668949 134203988500016859781357)
                  ·
                    rfl

theorem cell21_588063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 6].length) (baseStart_588063 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_588063 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_588063 prefixEnd_588063 := by exact prefixLift 588063
  have htrace : WordTrace (prefixWord ++ tailWord_588063) baseStart_588063 baseEnd_588063 := by
    simpa [prefixWord, tailWord_588063, baseEnd_588063] using wordTrace_append hprefix tailTrace_588063
  have hstable : (prefixWord ++ tailWord_588063).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588063).length < 2 ^ (prefixWord ++ tailWord_588063).sum := by decide
  have hdescent : baseEnd_588063 < baseStart_588063 := by decide
  rcases family_descends (prefixWord ++ tailWord_588063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588094 : List Nat := [4, 2, 1, 2, 1, 2, 1, 8]
def baseStart_588094 : Nat := 118140960795 + 588094 * 2 ^ 59
def prefixEnd_588094 : Nat := 4983230072969 + 3 ^ 40 * 588094 * 2
def baseEnd_588094 : Nat := 44737021040789231588209

theorem tailTrace_588094 : CollatzResearch.WordTrace tailWord_588094 prefixEnd_588094 44737021040789231588209 := by
  unfold tailWord_588094
  simp only [CollatzResearch.WordTrace]
  refine ⟨2681193791430418912999417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14299700220962234202663557 2681193791430418912999417)
  ·
    refine ⟨2010895343572814184749563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2681193791430418912999417 2010895343572814184749563)
    ·
      refine ⟨3016343015359221277124345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2010895343572814184749563 3016343015359221277124345)
      ·
        refine ⟨2262257261519415957843259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3016343015359221277124345 2262257261519415957843259)
        ·
          refine ⟨3393385892279123936764889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2262257261519415957843259 3393385892279123936764889)
          ·
            refine ⟨2545039419209342952573667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3393385892279123936764889 2545039419209342952573667)
            ·
              refine ⟨3817559128814014428860501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2545039419209342952573667 3817559128814014428860501)
              ·
                refine ⟨44737021040789231588209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3817559128814014428860501 44737021040789231588209)
                ·
                  rfl

theorem cell21_588094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 8].length) (baseStart_588094 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_588094 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_588094 prefixEnd_588094 := by exact prefixLift 588094
  have htrace : WordTrace (prefixWord ++ tailWord_588094) baseStart_588094 baseEnd_588094 := by
    simpa [prefixWord, tailWord_588094, baseEnd_588094] using wordTrace_append hprefix tailTrace_588094
  have hstable : (prefixWord ++ tailWord_588094).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588094).length < 2 ^ (prefixWord ++ tailWord_588094).sum := by decide
  have hdescent : baseEnd_588094 < baseStart_588094 := by decide
  rcases family_descends (prefixWord ++ tailWord_588094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588097 : List Nat := [1, 2, 5, 2, 2, 1, 1, 3, 4]
def baseStart_588097 : Nat := 118140960795 + 588097 * 2 ^ 59
def prefixEnd_588097 : Nat := 4983230072969 + 3 ^ 40 * 588097 * 2
def baseEnd_588097 : Nat := 134211747763240356214621

theorem tailTrace_588097 : CollatzResearch.WordTrace tailWord_588097 prefixEnd_588097 134211747763240356214621 := by
  unfold tailWord_588097
  simp only [CollatzResearch.WordTrace]
  refine ⟨21449659750432482816354545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14299773166954988544236363 21449659750432482816354545)
  ·
    refine ⟨16087244812824362112265909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21449659750432482816354545 16087244812824362112265909)
    ·
      refine ⟨1508179201202283948024929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16087244812824362112265909 1508179201202283948024929)
      ·
        refine ⟨1131134400901712961018697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1508179201202283948024929 1131134400901712961018697)
        ·
          refine ⟨848350800676284720764023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1131134400901712961018697 848350800676284720764023)
          ·
            refine ⟨1272526201014427081146035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 848350800676284720764023 1272526201014427081146035)
            ·
              refine ⟨1908789301521640621719053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1272526201014427081146035 1908789301521640621719053)
              ·
                refine ⟨715795988070615233144645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1908789301521640621719053 715795988070615233144645)
                ·
                  refine ⟨134211747763240356214621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 715795988070615233144645 134211747763240356214621)
                  ·
                    rfl

theorem cell21_588097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 3, 4].length) (baseStart_588097 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_588097 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_588097 prefixEnd_588097 := by exact prefixLift 588097
  have htrace : WordTrace (prefixWord ++ tailWord_588097) baseStart_588097 baseEnd_588097 := by
    simpa [prefixWord, tailWord_588097, baseEnd_588097] using wordTrace_append hprefix tailTrace_588097
  have hstable : (prefixWord ++ tailWord_588097).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588097).length < 2 ^ (prefixWord ++ tailWord_588097).sum := by decide
  have hdescent : baseEnd_588097 < baseStart_588097 := by decide
  rcases family_descends (prefixWord ++ tailWord_588097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588108 : List Nat := [2, 2, 1, 3, 2, 1, 2, 1, 7]
def baseStart_588108 : Nat := 118140960795 + 588108 * 2 ^ 59
def prefixEnd_588108 : Nat := 4983230072969 + 3 ^ 40 * 588108 * 2
def baseEnd_588108 : Nat := 134214258113106781531265

theorem tailTrace_588108 : CollatzResearch.WordTrace tailWord_588108 prefixEnd_588108 134214258113106781531265 := by
  unfold tailWord_588108
  simp only [CollatzResearch.WordTrace]
  refine ⟨10725030476696315847502489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14300040635595087796669985 10725030476696315847502489)
  ·
    refine ⟨8043772857522236885626867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10725030476696315847502489 8043772857522236885626867)
    ·
      refine ⟨12065659286283355328440301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8043772857522236885626867 12065659286283355328440301)
      ·
        refine ⟨4524622232356258248165113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12065659286283355328440301 4524622232356258248165113)
        ·
          refine ⟨3393466674267193686123835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4524622232356258248165113 3393466674267193686123835)
          ·
            refine ⟨5090200011400790529185753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3393466674267193686123835 5090200011400790529185753)
            ·
              refine ⟨3817650008550592896889315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5090200011400790529185753 3817650008550592896889315)
              ·
                refine ⟨5726475012825889345333973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3817650008550592896889315 5726475012825889345333973)
                ·
                  refine ⟨134214258113106781531265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5726475012825889345333973 134214258113106781531265)
                  ·
                    rfl

theorem cell21_588108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 7].length) (baseStart_588108 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_588108 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_588108 prefixEnd_588108 := by exact prefixLift 588108
  have htrace : WordTrace (prefixWord ++ tailWord_588108) baseStart_588108 baseEnd_588108 := by
    simpa [prefixWord, tailWord_588108, baseEnd_588108] using wordTrace_append hprefix tailTrace_588108
  have hstable : (prefixWord ++ tailWord_588108).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588108).length < 2 ^ (prefixWord ++ tailWord_588108).sum := by decide
  have hdescent : baseEnd_588108 < baseStart_588108 := by decide
  rcases family_descends (prefixWord ++ tailWord_588108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588190 : List Nat := [4, 3, 1, 2, 1, 3, 1, 2, 4]
def baseStart_588190 : Nat := 118140960795 + 588190 * 2 ^ 59
def prefixEnd_588190 : Nat := 4983230072969 + 3 ^ 40 * 588190 * 2
def baseEnd_588190 : Nat := 134232971630292861164431

theorem tailTrace_588190 : CollatzResearch.WordTrace tailWord_588190 prefixEnd_588190 134232971630292861164431 := by
  unfold tailWord_588190
  simp only [CollatzResearch.WordTrace]
  refine ⟨2681631467386944962436253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14302034492730373132993349 2681631467386944962436253)
  ·
    refine ⟨1005611800270104360913595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2681631467386944962436253 1005611800270104360913595)
    ·
      refine ⟨1508417700405156541370393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1005611800270104360913595 1508417700405156541370393)
      ·
        refine ⟨1131313275303867406027795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1508417700405156541370393 1131313275303867406027795)
        ·
          refine ⟨1696969912955801109041693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1131313275303867406027795 1696969912955801109041693)
          ·
            refine ⟨636363717358425415890635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1696969912955801109041693 636363717358425415890635)
            ·
              refine ⟨954545576037638123835953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 636363717358425415890635 954545576037638123835953)
              ·
                refine ⟨715909182028228592876965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 954545576037638123835953 715909182028228592876965)
                ·
                  refine ⟨134232971630292861164431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 715909182028228592876965 134232971630292861164431)
                  ·
                    rfl

theorem cell21_588190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_588190 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_588190 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_588190 prefixEnd_588190 := by exact prefixLift 588190
  have htrace : WordTrace (prefixWord ++ tailWord_588190) baseStart_588190 baseEnd_588190 := by
    simpa [prefixWord, tailWord_588190, baseEnd_588190] using wordTrace_append hprefix tailTrace_588190
  have hstable : (prefixWord ++ tailWord_588190).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588190).length < 2 ^ (prefixWord ++ tailWord_588190).sum := by decide
  have hdescent : baseEnd_588190 < baseStart_588190 := by decide
  rcases family_descends (prefixWord ++ tailWord_588190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588311 : List Nat := [1, 1, 3, 6, 1, 1, 1, 4, 3]
def baseStart_588311 : Nat := 118140960795 + 588311 * 2 ^ 59
def prefixEnd_588311 : Nat := 4983230072969 + 3 ^ 40 * 588311 * 2
def baseEnd_588311 : Nat := 134260585478823539647517

theorem tailTrace_588311 : CollatzResearch.WordTrace tailWord_588311 prefixEnd_588311 134260585478823539647517 := by
  unfold tailWord_588311
  simp only [CollatzResearch.WordTrace]
  refine ⟨21457464971657197364644787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14304976647771464909763191 21457464971657197364644787)
  ·
    refine ⟨32186197457485796046967181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21457464971657197364644787 32186197457485796046967181)
    ·
      refine ⟨12069824046557173517612693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32186197457485796046967181 12069824046557173517612693)
      ·
        refine ⟨565773002182367508638095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 12069824046557173517612693 565773002182367508638095)
        ·
          refine ⟨848659503273551262957143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 565773002182367508638095 848659503273551262957143)
          ·
            refine ⟨1272989254910326894435715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 848659503273551262957143 1272989254910326894435715)
            ·
              refine ⟨1909483882365490341653573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1272989254910326894435715 1909483882365490341653573)
              ·
                refine ⟨358028227943529439060045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1909483882365490341653573 358028227943529439060045)
                ·
                  refine ⟨134260585478823539647517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 358028227943529439060045 134260585478823539647517)
                  ·
                    rfl

theorem cell21_588311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 4, 3].length) (baseStart_588311 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_588311 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_588311 prefixEnd_588311 := by exact prefixLift 588311
  have htrace : WordTrace (prefixWord ++ tailWord_588311) baseStart_588311 baseEnd_588311 := by
    simpa [prefixWord, tailWord_588311, baseEnd_588311] using wordTrace_append hprefix tailTrace_588311
  have hstable : (prefixWord ++ tailWord_588311).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588311).length < 2 ^ (prefixWord ++ tailWord_588311).sum := by decide
  have hdescent : baseEnd_588311 < baseStart_588311 := by decide
  rcases family_descends (prefixWord ++ tailWord_588311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588356 : List Nat := [2, 3, 5, 1, 1, 1, 8]
def baseStart_588356 : Nat := 118140960795 + 588356 * 2 ^ 59
def prefixEnd_588356 : Nat := 4983230072969 + 3 ^ 40 * 588356 * 2
def baseEnd_588356 : Nat := 14918983899101495710825

theorem tailTrace_588356 : CollatzResearch.WordTrace tailWord_588356 prefixEnd_588356 14918983899101495710825 := by
  unfold tailWord_588356
  simp only [CollatzResearch.WordTrace]
  refine ⟨10729553128247085025016461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14306070837662780033355281 10729553128247085025016461)
  ·
    refine ⟨4023582423092656884381173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10729553128247085025016461 4023582423092656884381173)
    ·
      refine ⟨377210852164936582910735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4023582423092656884381173 377210852164936582910735)
      ·
        refine ⟨565816278247404874366103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 377210852164936582910735 565816278247404874366103)
        ·
          refine ⟨848724417371107311549155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 565816278247404874366103 848724417371107311549155)
          ·
            refine ⟨1273086626056660967323733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 848724417371107311549155 1273086626056660967323733)
            ·
              refine ⟨14918983899101495710825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1273086626056660967323733 14918983899101495710825)
              ·
                rfl

theorem cell21_588356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 8].length) (baseStart_588356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_588356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_588356 prefixEnd_588356 := by exact prefixLift 588356
  have htrace : WordTrace (prefixWord ++ tailWord_588356) baseStart_588356 baseEnd_588356 := by
    simpa [prefixWord, tailWord_588356, baseEnd_588356] using wordTrace_append hprefix tailTrace_588356
  have hstable : (prefixWord ++ tailWord_588356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588356).length < 2 ^ (prefixWord ++ tailWord_588356).sum := by decide
  have hdescent : baseEnd_588356 < baseStart_588356 := by decide
  rcases family_descends (prefixWord ++ tailWord_588356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588367 : List Nat := [1, 1, 2, 1, 1, 2, 7, 2, 4]
def baseStart_588367 : Nat := 118140960795 + 588367 * 2 ^ 59
def prefixEnd_588367 : Nat := 4983230072969 + 3 ^ 40 * 588367 * 2
def baseEnd_588367 : Nat := 134273365441779886714069

theorem tailTrace_588367 : CollatzResearch.WordTrace tailWord_588367 prefixEnd_588367 134273365441779886714069 := by
  unfold tailWord_588367
  simp only [CollatzResearch.WordTrace]
  refine ⟨21459507459454318928683355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14306338306302879285788903 21459507459454318928683355)
  ·
    refine ⟨32189261189181478393025033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21459507459454318928683355 32189261189181478393025033)
    ·
      refine ⟨24141945891886108794768775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32189261189181478393025033 24141945891886108794768775)
      ·
        refine ⟨36212918837829163192153163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24141945891886108794768775 36212918837829163192153163)
        ·
          refine ⟨54319378256743744788229745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36212918837829163192153163 54319378256743744788229745)
          ·
            refine ⟨40739533692557808591172309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54319378256743744788229745 40739533692557808591172309)
            ·
              refine ⟨954832820919323638855601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 40739533692557808591172309 954832820919323638855601)
              ·
                refine ⟨716124615689492729141701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 954832820919323638855601 716124615689492729141701)
                ·
                  refine ⟨134273365441779886714069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 716124615689492729141701 134273365441779886714069)
                  ·
                    rfl

theorem cell21_588367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 2, 4].length) (baseStart_588367 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_588367 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_588367 prefixEnd_588367 := by exact prefixLift 588367
  have htrace : WordTrace (prefixWord ++ tailWord_588367) baseStart_588367 baseEnd_588367 := by
    simpa [prefixWord, tailWord_588367, baseEnd_588367] using wordTrace_append hprefix tailTrace_588367
  have hstable : (prefixWord ++ tailWord_588367).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588367).length < 2 ^ (prefixWord ++ tailWord_588367).sum := by decide
  have hdescent : baseEnd_588367 < baseStart_588367 := by decide
  rcases family_descends (prefixWord ++ tailWord_588367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588395 : List Nat := [1, 1, 1, 1, 2, 2, 1, 5, 7]
def baseStart_588395 : Nat := 118140960795 + 588395 * 2 ^ 59
def prefixEnd_588395 : Nat := 4983230072969 + 3 ^ 40 * 588395 * 2
def baseEnd_588395 : Nat := 134279755423258060247345

theorem tailTrace_588395 : CollatzResearch.WordTrace tailWord_588395 prefixEnd_588395 134279755423258060247345 := by
  unfold tailWord_588395
  simp only [CollatzResearch.WordTrace]
  refine ⟨21460528703352879710702639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14307019135568586473801759 21460528703352879710702639)
  ·
    refine ⟨32190793055029319566053959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21460528703352879710702639 32190793055029319566053959)
    ·
      refine ⟨48286189582543979349080939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32190793055029319566053959 48286189582543979349080939)
      ·
        refine ⟨72429284373815969023621409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48286189582543979349080939 72429284373815969023621409)
        ·
          refine ⟨54321963280361976767716057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72429284373815969023621409 54321963280361976767716057)
          ·
            refine ⟨40741472460271482575787043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54321963280361976767716057 40741472460271482575787043)
            ·
              refine ⟨61112208690407223863680565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40741472460271482575787043 61112208690407223863680565)
              ·
                refine ⟨5729269564725677237220053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61112208690407223863680565 5729269564725677237220053)
                ·
                  refine ⟨134279755423258060247345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5729269564725677237220053 134279755423258060247345)
                  ·
                    rfl

theorem cell21_588395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 7].length) (baseStart_588395 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_588395 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_588395 prefixEnd_588395 := by exact prefixLift 588395
  have htrace : WordTrace (prefixWord ++ tailWord_588395) baseStart_588395 baseEnd_588395 := by
    simpa [prefixWord, tailWord_588395, baseEnd_588395] using wordTrace_append hprefix tailTrace_588395
  have hstable : (prefixWord ++ tailWord_588395).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588395).length < 2 ^ (prefixWord ++ tailWord_588395).sum := by decide
  have hdescent : baseEnd_588395 < baseStart_588395 := by decide
  rcases family_descends (prefixWord ++ tailWord_588395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588398 : List Nat := [4, 1, 2, 2, 2, 2, 1, 7]
def baseStart_588398 : Nat := 118140960795 + 588398 * 2 ^ 59
def prefixEnd_588398 : Nat := 4983230072969 + 3 ^ 40 * 588398 * 2
def baseEnd_588398 : Nat := 44760146688043573899113

theorem tailTrace_588398 : CollatzResearch.WordTrace tailWord_588398 prefixEnd_588398 44760146688043573899113 := by
  unfold tailWord_588398
  simp only [CollatzResearch.WordTrace]
  refine ⟨2682579765292751402882731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14307092081561340815374565 2682579765292751402882731)
  ·
    refine ⟨4023869647939127104324097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2682579765292751402882731 4023869647939127104324097)
    ·
      refine ⟨3017902235954345328243073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4023869647939127104324097 3017902235954345328243073)
      ·
        refine ⟨2263426676965758996182305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3017902235954345328243073 2263426676965758996182305)
        ·
          refine ⟨1697570007724319247136729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2263426676965758996182305 1697570007724319247136729)
          ·
            refine ⟨1273177505793239435352547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1697570007724319247136729 1273177505793239435352547)
            ·
              refine ⟨1909766258689859153028821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1273177505793239435352547 1909766258689859153028821)
              ·
                refine ⟨44760146688043573899113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1909766258689859153028821 44760146688043573899113)
                ·
                  rfl

theorem cell21_588398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 7].length) (baseStart_588398 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_588398 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_588398 prefixEnd_588398 := by exact prefixLift 588398
  have htrace : WordTrace (prefixWord ++ tailWord_588398) baseStart_588398 baseEnd_588398 := by
    simpa [prefixWord, tailWord_588398, baseEnd_588398] using wordTrace_append hprefix tailTrace_588398
  have hstable : (prefixWord ++ tailWord_588398).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588398).length < 2 ^ (prefixWord ++ tailWord_588398).sum := by decide
  have hdescent : baseEnd_588398 < baseStart_588398 := by decide
  rcases family_descends (prefixWord ++ tailWord_588398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588567 : List Nat := [1, 1, 3, 4, 3, 2, 2, 5]
def baseStart_588567 : Nat := 118140960795 + 588567 * 2 ^ 59
def prefixEnd_588567 : Nat := 4983230072969 + 3 ^ 40 * 588567 * 2
def baseEnd_588567 : Nat := 44773002722207994460109

theorem tailTrace_588567 : CollatzResearch.WordTrace tailWord_588567 prefixEnd_588567 44773002722207994460109 := by
  unfold tailWord_588567
  simp only [CollatzResearch.WordTrace]
  refine ⟨21466802058729753085963955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14311201372486502057309303 21466802058729753085963955)
  ·
    refine ⟨32200203088094629628945933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21466802058729753085963955 32200203088094629628945933)
    ·
      refine ⟨12075076158035486110854725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32200203088094629628945933 12075076158035486110854725)
      ·
        refine ⟨2264076779631653645785261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12075076158035486110854725 2264076779631653645785261)
        ·
          refine ⟨849028792361870117169473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2264076779631653645785261 849028792361870117169473)
          ·
            refine ⟨636771594271402587877105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 849028792361870117169473 636771594271402587877105)
            ·
              refine ⟨477578695703551940907829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 636771594271402587877105 477578695703551940907829)
              ·
                refine ⟨44773002722207994460109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 477578695703551940907829 44773002722207994460109)
                ·
                  rfl

theorem cell21_588567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 5].length) (baseStart_588567 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_588567 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_588567 prefixEnd_588567 := by exact prefixLift 588567
  have htrace : WordTrace (prefixWord ++ tailWord_588567) baseStart_588567 baseEnd_588567 := by
    simpa [prefixWord, tailWord_588567, baseEnd_588567] using wordTrace_append hprefix tailTrace_588567
  have hstable : (prefixWord ++ tailWord_588567).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588567).length < 2 ^ (prefixWord ++ tailWord_588567).sum := by decide
  have hdescent : baseEnd_588567 < baseStart_588567 := by decide
  rcases family_descends (prefixWord ++ tailWord_588567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588657 : List Nat := [1, 2, 2, 2, 1, 5, 1, 4, 3]
def baseStart_588657 : Nat := 118140960795 + 588657 * 2 ^ 59
def prefixEnd_588657 : Nat := 4983230072969 + 3 ^ 40 * 588657 * 2
def baseEnd_588657 : Nat := 134339547392803826880143

theorem tailTrace_588657 : CollatzResearch.WordTrace tailWord_588657 prefixEnd_588657 134339547392803826880143 := by
  unfold tailWord_588657
  simp only [CollatzResearch.WordTrace]
  refine ⟨21470084628403698456740225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14313389752269132304493483 21470084628403698456740225)
  ·
    refine ⟨16102563471302773842555169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21470084628403698456740225 16102563471302773842555169)
    ·
      refine ⟨12076922603477080381916377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16102563471302773842555169 12076922603477080381916377)
      ·
        refine ⟨9057691952607810286437283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12076922603477080381916377 9057691952607810286437283)
        ·
          refine ⟨13586537928911715429655925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9057691952607810286437283 13586537928911715429655925)
          ·
            refine ⟨1273737930835473321530243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13586537928911715429655925 1273737930835473321530243)
            ·
              refine ⟨1910606896253209982295365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1273737930835473321530243 1910606896253209982295365)
              ·
                refine ⟨358238793047476871680381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1910606896253209982295365 358238793047476871680381)
                ·
                  refine ⟨134339547392803826880143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 358238793047476871680381 134339547392803826880143)
                  ·
                    rfl

theorem cell21_588657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 4, 3].length) (baseStart_588657 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_588657 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_588657 prefixEnd_588657 := by exact prefixLift 588657
  have htrace : WordTrace (prefixWord ++ tailWord_588657) baseStart_588657 baseEnd_588657 := by
    simpa [prefixWord, tailWord_588657, baseEnd_588657] using wordTrace_append hprefix tailTrace_588657
  have hstable : (prefixWord ++ tailWord_588657).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588657).length < 2 ^ (prefixWord ++ tailWord_588657).sum := by decide
  have hdescent : baseEnd_588657 < baseStart_588657 := by decide
  rcases family_descends (prefixWord ++ tailWord_588657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588742 : List Nat := [6, 1, 3, 1, 1, 2, 1, 3, 3]
def baseStart_588742 : Nat := 118140960795 + 588742 * 2 ^ 59
def prefixEnd_588742 : Nat := 4983230072969 + 3 ^ 40 * 588742 * 2
def baseEnd_588742 : Nat := 134358945550862567963303

theorem tailTrace_588742 : CollatzResearch.WordTrace tailWord_588742 prefixEnd_588742 134358945550862567963303 := by
  unfold tailWord_588742
  simp only [CollatzResearch.WordTrace]
  refine ⟨671037026034242436674515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14315456555397171982389653 671037026034242436674515)
  ·
    refine ⟨1006555539051363655011773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 671037026034242436674515 1006555539051363655011773)
    ·
      refine ⟨377458327144261370629415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1006555539051363655011773 377458327144261370629415)
      ·
        refine ⟨566187490716392055944123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 377458327144261370629415 566187490716392055944123)
        ·
          refine ⟨849281236074588083916185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 566187490716392055944123 849281236074588083916185)
          ·
            refine ⟨636960927055941062937139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 849281236074588083916185 636960927055941062937139)
            ·
              refine ⟨955441390583911594405709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 636960927055941062937139 955441390583911594405709)
              ·
                refine ⟨358290521468966847902141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 955441390583911594405709 358290521468966847902141)
                ·
                  refine ⟨134358945550862567963303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 358290521468966847902141 134358945550862567963303)
                  ·
                    rfl

theorem cell21_588742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_588742 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_588742 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_588742 prefixEnd_588742 := by exact prefixLift 588742
  have htrace : WordTrace (prefixWord ++ tailWord_588742) baseStart_588742 baseEnd_588742 := by
    simpa [prefixWord, tailWord_588742, baseEnd_588742] using wordTrace_append hprefix tailTrace_588742
  have hstable : (prefixWord ++ tailWord_588742).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588742).length < 2 ^ (prefixWord ++ tailWord_588742).sum := by decide
  have hdescent : baseEnd_588742 < baseStart_588742 := by decide
  rcases family_descends (prefixWord ++ tailWord_588742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588750 : List Nat := [4, 1, 1, 1, 2, 5, 1, 3, 3]
def baseStart_588750 : Nat := 118140960795 + 588750 * 2 ^ 59
def prefixEnd_588750 : Nat := 4983230072969 + 3 ^ 40 * 588750 * 2
def baseEnd_588750 : Nat := 134360771259856331829953

theorem tailTrace_588750 : CollatzResearch.WordTrace tailWord_588750 prefixEnd_588750 134360771259856331829953 := by
  unfold tailWord_588750
  simp only [CollatzResearch.WordTrace]
  refine ⟨2684184577133346917484463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14315651078044516893250469 2684184577133346917484463)
  ·
    refine ⟨4026276865700020376226695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2684184577133346917484463 4026276865700020376226695)
    ·
      refine ⟨6039415298550030564340043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4026276865700020376226695 6039415298550030564340043)
      ·
        refine ⟨9059122947825045846510065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6039415298550030564340043 9059122947825045846510065)
        ·
          refine ⟨6794342210868784384882549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9059122947825045846510065 6794342210868784384882549)
          ·
            refine ⟨636969582268948536082739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6794342210868784384882549 636969582268948536082739)
            ·
              refine ⟨955454373403422804124109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 636969582268948536082739 955454373403422804124109)
              ·
                refine ⟨358295390026283551546541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 955454373403422804124109 358295390026283551546541)
                ·
                  refine ⟨134360771259856331829953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 358295390026283551546541 134360771259856331829953)
                  ·
                    rfl

theorem cell21_588750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 3, 3].length) (baseStart_588750 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_588750 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_588750 prefixEnd_588750 := by exact prefixLift 588750
  have htrace : WordTrace (prefixWord ++ tailWord_588750) baseStart_588750 baseEnd_588750 := by
    simpa [prefixWord, tailWord_588750, baseEnd_588750] using wordTrace_append hprefix tailTrace_588750
  have hstable : (prefixWord ++ tailWord_588750).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588750).length < 2 ^ (prefixWord ++ tailWord_588750).sum := by decide
  have hdescent : baseEnd_588750 < baseStart_588750 := by decide
  rcases family_descends (prefixWord ++ tailWord_588750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588761 : List Nat := [1, 2, 1, 2, 5, 3, 7]
def baseStart_588761 : Nat := 118140960795 + 588761 * 2 ^ 59
def prefixEnd_588761 : Nat := 4983230072969 + 3 ^ 40 * 588761 * 2
def baseEnd_588761 : Nat := 14929253512191417460733

theorem tailTrace_588761 : CollatzResearch.WordTrace tailWord_588761 prefixEnd_588761 14929253512191417460733 := by
  unfold tailWord_588761
  simp only [CollatzResearch.WordTrace]
  refine ⟨21473877820026924218526137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14315918546684616145684091 21473877820026924218526137)
  ·
    refine ⟨16105408365020193163894603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21473877820026924218526137 16105408365020193163894603)
    ·
      refine ⟨24158112547530289745841905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16105408365020193163894603 24158112547530289745841905)
      ·
        refine ⟨18118584410647717309381429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24158112547530289745841905 18118584410647717309381429)
        ·
          refine ⟨1698617288498223497754509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18118584410647717309381429 1698617288498223497754509)
          ·
            refine ⟨636981483186833811657941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1698617288498223497754509 636981483186833811657941)
            ·
              refine ⟨14929253512191417460733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 636981483186833811657941 14929253512191417460733)
              ·
                rfl

theorem cell21_588761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 7].length) (baseStart_588761 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_588761 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_588761 prefixEnd_588761 := by exact prefixLift 588761
  have htrace : WordTrace (prefixWord ++ tailWord_588761) baseStart_588761 baseEnd_588761 := by
    simpa [prefixWord, tailWord_588761, baseEnd_588761] using wordTrace_append hprefix tailTrace_588761
  have hstable : (prefixWord ++ tailWord_588761).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588761).length < 2 ^ (prefixWord ++ tailWord_588761).sum := by decide
  have hdescent : baseEnd_588761 < baseStart_588761 := by decide
  rcases family_descends (prefixWord ++ tailWord_588761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588818 : List Nat := [3, 2, 5, 1, 2, 1, 2, 2, 3]
def baseStart_588818 : Nat := 118140960795 + 588818 * 2 ^ 59
def prefixEnd_588818 : Nat := 4983230072969 + 3 ^ 40 * 588818 * 2
def baseEnd_588818 : Nat := 134376289786303324696481

theorem tailTrace_588818 : CollatzResearch.WordTrace tailWord_588818 prefixEnd_588818 134376289786303324696481 := by
  unfold tailWord_588818
  simp only [CollatzResearch.WordTrace]
  refine ⟨5368989195205105738337777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14317304520546948635567405 5368989195205105738337777)
  ·
    refine ⟨4026741896403829303753333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5368989195205105738337777 4026741896403829303753333)
    ·
      refine ⟨377507052787858997226875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4026741896403829303753333 377507052787858997226875)
      ·
        refine ⟨566260579181788495840313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 377507052787858997226875 566260579181788495840313)
        ·
          refine ⟨424695434386341371880235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 566260579181788495840313 424695434386341371880235)
          ·
            refine ⟨637043151579512057820353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 424695434386341371880235 637043151579512057820353)
            ·
              refine ⟨477782363684634043365265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 637043151579512057820353 477782363684634043365265)
              ·
                refine ⟨358336772763475532523949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 477782363684634043365265 358336772763475532523949)
                ·
                  refine ⟨134376289786303324696481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 358336772763475532523949 134376289786303324696481)
                  ·
                    rfl

theorem cell21_588818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 2, 3].length) (baseStart_588818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_588818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_588818 prefixEnd_588818 := by exact prefixLift 588818
  have htrace : WordTrace (prefixWord ++ tailWord_588818) baseStart_588818 baseEnd_588818 := by
    simpa [prefixWord, tailWord_588818, baseEnd_588818] using wordTrace_append hprefix tailTrace_588818
  have hstable : (prefixWord ++ tailWord_588818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588818).length < 2 ^ (prefixWord ++ tailWord_588818).sum := by decide
  have hdescent : baseEnd_588818 < baseStart_588818 := by decide
  rcases family_descends (prefixWord ++ tailWord_588818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588823 : List Nat := [1, 1, 3, 5, 1, 1, 1, 4, 4]
def baseStart_588823 : Nat := 118140960795 + 588823 * 2 ^ 59
def prefixEnd_588823 : Nat := 4983230072969 + 3 ^ 40 * 588823 * 2
def baseEnd_588823 : Nat := 134377430854424427113137

theorem tailTrace_588823 : CollatzResearch.WordTrace tailWord_588823 prefixEnd_588823 134377430854424427113137 := by
  unfold tailWord_588823
  simp only [CollatzResearch.WordTrace]
  refine ⟨21476139145802308807283123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14317426097201539204855415 21476139145802308807283123)
  ·
    refine ⟨32214208718703463210924685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21476139145802308807283123 32214208718703463210924685)
    ·
      refine ⟨12080328269513798704096757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32214208718703463210924685 12080328269513798704096757)
      ·
        refine ⟨1132530775266918628509071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12080328269513798704096757 1132530775266918628509071)
        ·
          refine ⟨1698796162900377942763607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1132530775266918628509071 1698796162900377942763607)
          ·
            refine ⟨2548194244350566914145411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1698796162900377942763607 2548194244350566914145411)
            ·
              refine ⟨3822291366525850371218117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2548194244350566914145411 3822291366525850371218117)
              ·
                refine ⟨716679631223596944603397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3822291366525850371218117 716679631223596944603397)
                ·
                  refine ⟨134377430854424427113137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 716679631223596944603397 134377430854424427113137)
                  ·
                    rfl

theorem cell21_588823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 4, 4].length) (baseStart_588823 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_588823 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_588823 prefixEnd_588823 := by exact prefixLift 588823
  have htrace : WordTrace (prefixWord ++ tailWord_588823) baseStart_588823 baseEnd_588823 := by
    simpa [prefixWord, tailWord_588823, baseEnd_588823] using wordTrace_append hprefix tailTrace_588823
  have hstable : (prefixWord ++ tailWord_588823).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588823).length < 2 ^ (prefixWord ++ tailWord_588823).sum := by decide
  have hdescent : baseEnd_588823 < baseStart_588823 := by decide
  rcases family_descends (prefixWord ++ tailWord_588823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588896 : List Nat := [2, 1, 1, 3, 2, 2, 2, 8]
def baseStart_588896 : Nat := 118140960795 + 588896 * 2 ^ 59
def prefixEnd_588896 : Nat := 4983230072969 + 3 ^ 40 * 588896 * 2
def baseEnd_588896 : Nat := 44798030149664174132107

theorem tailTrace_588896 : CollatzResearch.WordTrace tailWord_588896 prefixEnd_588896 44798030149664174132107 := by
  unfold tailWord_588896
  simp only [CollatzResearch.WordTrace]
  refine ⟨10739400837268921137345271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14319201116358561516460361 10739400837268921137345271)
  ·
    refine ⟨16109101255903381706017907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10739400837268921137345271 16109101255903381706017907)
    ·
      refine ⟨24163651883855072559026861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16109101255903381706017907 24163651883855072559026861)
      ·
        refine ⟨9061369456445652209635073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24163651883855072559026861 9061369456445652209635073)
        ·
          refine ⟨6796027092334239157226305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9061369456445652209635073 6796027092334239157226305)
          ·
            refine ⟨5097020319250679367919729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6796027092334239157226305 5097020319250679367919729)
            ·
              refine ⟨3822765239438009525939797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5097020319250679367919729 3822765239438009525939797)
              ·
                refine ⟨44798030149664174132107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3822765239438009525939797 44798030149664174132107)
                ·
                  rfl

theorem cell21_588896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 8].length) (baseStart_588896 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_588896 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_588896 prefixEnd_588896 := by exact prefixLift 588896
  have htrace : WordTrace (prefixWord ++ tailWord_588896) baseStart_588896 baseEnd_588896 := by
    simpa [prefixWord, tailWord_588896, baseEnd_588896] using wordTrace_append hprefix tailTrace_588896
  have hstable : (prefixWord ++ tailWord_588896).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588896).length < 2 ^ (prefixWord ++ tailWord_588896).sum := by decide
  have hdescent : baseEnd_588896 < baseStart_588896 := by decide
  rcases family_descends (prefixWord ++ tailWord_588896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589006 : List Nat := [4, 1, 1, 1, 5, 2, 1, 6]
def baseStart_589006 : Nat := 118140960795 + 589006 * 2 ^ 59
def prefixEnd_589006 : Nat := 4983230072969 + 3 ^ 40 * 589006 * 2
def baseEnd_589006 : Nat := 44806397982552258520921

theorem tailTrace_589006 : CollatzResearch.WordTrace tailWord_589006 prefixEnd_589006 44806397982552258520921 := by
  unfold tailWord_589006
  simp only [CollatzResearch.WordTrace]
  refine ⟨2685351713017416382649359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14321875802759554040796581 2685351713017416382649359)
  ·
    refine ⟨4028027569526124573974039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2685351713017416382649359 4028027569526124573974039)
    ·
      refine ⟨6042041354289186860961059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4028027569526124573974039 6042041354289186860961059)
      ·
        refine ⟨9063062031433780291441589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6042041354289186860961059 9063062031433780291441589)
        ·
          refine ⟨849662065446916902322649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9063062031433780291441589 849662065446916902322649)
          ·
            refine ⟨637246549085187676741987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 849662065446916902322649 637246549085187676741987)
            ·
              refine ⟨955869823627781515112981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 637246549085187676741987 955869823627781515112981)
              ·
                refine ⟨44806397982552258520921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 955869823627781515112981 44806397982552258520921)
                ·
                  rfl

theorem cell21_589006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 6].length) (baseStart_589006 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_589006 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_589006 prefixEnd_589006 := by exact prefixLift 589006
  have htrace : WordTrace (prefixWord ++ tailWord_589006) baseStart_589006 baseEnd_589006 := by
    simpa [prefixWord, tailWord_589006, baseEnd_589006] using wordTrace_append hprefix tailTrace_589006
  have hstable : (prefixWord ++ tailWord_589006).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589006).length < 2 ^ (prefixWord ++ tailWord_589006).sum := by decide
  have hdescent : baseEnd_589006 < baseStart_589006 := by decide
  rcases family_descends (prefixWord ++ tailWord_589006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589017 : List Nat := [1, 2, 1, 2, 3, 1, 1, 2, 8]
def baseStart_589017 : Nat := 118140960795 + 589017 * 2 ^ 59
def prefixEnd_589017 : Nat := 4983230072969 + 3 ^ 40 * 589017 * 2
def baseEnd_589017 : Nat := 134421704297523200879407

theorem tailTrace_589017 : CollatzResearch.WordTrace tailWord_589017 prefixEnd_589017 134421704297523200879407 := by
  unfold tailWord_589017
  simp only [CollatzResearch.WordTrace]
  refine ⟨21483214907099479939845305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14322143271399653293230203 21483214907099479939845305)
  ·
    refine ⟨16112411180324609954883979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21483214907099479939845305 16112411180324609954883979)
    ·
      refine ⟨24168616770486914932325969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16112411180324609954883979 24168616770486914932325969)
      ·
        refine ⟨18126462577865186199244477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24168616770486914932325969 18126462577865186199244477)
        ·
          refine ⟨6797423466699444824716679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18126462577865186199244477 6797423466699444824716679)
          ·
            refine ⟨10196135200049167237075019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6797423466699444824716679 10196135200049167237075019)
            ·
              refine ⟨15294202800073750855612529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10196135200049167237075019 15294202800073750855612529)
              ·
                refine ⟨11470652100055313141709397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15294202800073750855612529 11470652100055313141709397)
                ·
                  refine ⟨134421704297523200879407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11470652100055313141709397 134421704297523200879407)
                  ·
                    rfl

theorem cell21_589017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 8].length) (baseStart_589017 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_589017 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_589017 prefixEnd_589017 := by exact prefixLift 589017
  have htrace : WordTrace (prefixWord ++ tailWord_589017) baseStart_589017 baseEnd_589017 := by
    simpa [prefixWord, tailWord_589017, baseEnd_589017] using wordTrace_append hprefix tailTrace_589017
  have hstable : (prefixWord ++ tailWord_589017).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589017).length < 2 ^ (prefixWord ++ tailWord_589017).sum := by decide
  have hdescent : baseEnd_589017 < baseStart_589017 := by decide
  rcases family_descends (prefixWord ++ tailWord_589017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589037 : List Nat := [1, 5, 1, 2, 2, 1, 1, 5, 3]
def baseStart_589037 : Nat := 118140960795 + 589037 * 2 ^ 59
def prefixEnd_589037 : Nat := 4983230072969 + 3 ^ 40 * 589037 * 2
def baseEnd_589037 : Nat := 134426268570007610546033

theorem tailTrace_589037 : CollatzResearch.WordTrace tailWord_589037 prefixEnd_589037 134426268570007610546033 := by
  unfold tailWord_589037
  simp only [CollatzResearch.WordTrace]
  refine ⟨21483944367027023355573365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14322629578018015570382243 21483944367027023355573365)
  ·
    refine ⟨2014119784408783439585003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21483944367027023355573365 2014119784408783439585003)
    ·
      refine ⟨3021179676613175159377505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2014119784408783439585003 3021179676613175159377505)
      ·
        refine ⟨2265884757459881369533129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3021179676613175159377505 2265884757459881369533129)
        ·
          refine ⟨1699413568094911027149847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2265884757459881369533129 1699413568094911027149847)
          ·
            refine ⟨2549120352142366540724771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1699413568094911027149847 2549120352142366540724771)
            ·
              refine ⟨3823680528213549811087157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2549120352142366540724771 3823680528213549811087157)
              ·
                refine ⟨358470049520020294789421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3823680528213549811087157 358470049520020294789421)
                ·
                  refine ⟨134426268570007610546033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 358470049520020294789421 134426268570007610546033)
                  ·
                    rfl

theorem cell21_589037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_589037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_589037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_589037 prefixEnd_589037 := by exact prefixLift 589037
  have htrace : WordTrace (prefixWord ++ tailWord_589037) baseStart_589037 baseEnd_589037 := by
    simpa [prefixWord, tailWord_589037, baseEnd_589037] using wordTrace_append hprefix tailTrace_589037
  have hstable : (prefixWord ++ tailWord_589037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589037).length < 2 ^ (prefixWord ++ tailWord_589037).sum := by decide
  have hdescent : baseEnd_589037 < baseStart_589037 := by decide
  rcases family_descends (prefixWord ++ tailWord_589037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589079 : List Nat := [1, 1, 3, 4, 1, 1, 1, 4, 5]
def baseStart_589079 : Nat := 118140960795 + 589079 * 2 ^ 59
def prefixEnd_589079 : Nat := 4983230072969 + 3 ^ 40 * 589079 * 2
def baseEnd_589079 : Nat := 134435853542224870845947

theorem tailTrace_589079 : CollatzResearch.WordTrace tailWord_589079 prefixEnd_589079 134435853542224870845947 := by
  unfold tailWord_589079
  simp only [CollatzResearch.WordTrace]
  refine ⟨21485476232874864528602291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14323650821916576352401527 21485476232874864528602291)
  ·
    refine ⟨32228214349312296792903437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21485476232874864528602291 32228214349312296792903437)
    ·
      refine ⟨12085580380992111297338789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32228214349312296792903437 12085580380992111297338789)
      ·
        refine ⟨2266046321436020868251023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12085580380992111297338789 2266046321436020868251023)
        ·
          refine ⟨3399069482154031302376535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2266046321436020868251023 3399069482154031302376535)
          ·
            refine ⟨5098604223231046953564803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3399069482154031302376535 5098604223231046953564803)
            ·
              refine ⟨7647906334846570430347205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5098604223231046953564803 7647906334846570430347205)
              ·
                refine ⟨1433982437783731955690101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7647906334846570430347205 1433982437783731955690101)
                ·
                  refine ⟨134435853542224870845947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1433982437783731955690101 134435853542224870845947)
                  ·
                    rfl

theorem cell21_589079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4, 5].length) (baseStart_589079 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_589079 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_589079 prefixEnd_589079 := by exact prefixLift 589079
  have htrace : WordTrace (prefixWord ++ tailWord_589079) baseStart_589079 baseEnd_589079 := by
    simpa [prefixWord, tailWord_589079, baseEnd_589079] using wordTrace_append hprefix tailTrace_589079
  have hstable : (prefixWord ++ tailWord_589079).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589079).length < 2 ^ (prefixWord ++ tailWord_589079).sum := by decide
  have hdescent : baseEnd_589079 < baseStart_589079 := by decide
  rcases family_descends (prefixWord ++ tailWord_589079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589082 : List Nat := [3, 1, 1, 3, 3, 3, 2, 5]
def baseStart_589082 : Nat := 118140960795 + 589082 * 2 ^ 59
def prefixEnd_589082 : Nat := 4983230072969 + 3 ^ 40 * 589082 * 2
def baseEnd_589082 : Nat := 44812179394365844098647

theorem tailTrace_589082 : CollatzResearch.WordTrace tailWord_589082 prefixEnd_589082 44812179394365844098647 := by
  unfold tailWord_589082
  simp only [CollatzResearch.WordTrace]
  refine ⟨5371396412965999010240375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14323723767909330693974333 5371396412965999010240375)
  ·
    refine ⟨8057094619448998515360563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5371396412965999010240375 8057094619448998515360563)
    ·
      refine ⟨12085641929173497773040845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8057094619448998515360563 12085641929173497773040845)
      ·
        refine ⟨4532115723440061664890317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12085641929173497773040845 4532115723440061664890317)
        ·
          refine ⟨1699543396290023124333869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4532115723440061664890317 1699543396290023124333869)
          ·
            refine ⟨637328773608758671625201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1699543396290023124333869 637328773608758671625201)
            ·
              refine ⟨477996580206569003718901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 637328773608758671625201 477996580206569003718901)
              ·
                refine ⟨44812179394365844098647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 477996580206569003718901 44812179394365844098647)
                ·
                  rfl

theorem cell21_589082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 5].length) (baseStart_589082 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_589082 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_589082 prefixEnd_589082 := by exact prefixLift 589082
  have htrace : WordTrace (prefixWord ++ tailWord_589082) baseStart_589082 baseEnd_589082 := by
    simpa [prefixWord, tailWord_589082, baseEnd_589082] using wordTrace_append hprefix tailTrace_589082
  have hstable : (prefixWord ++ tailWord_589082).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589082).length < 2 ^ (prefixWord ++ tailWord_589082).sum := by decide
  have hdescent : baseEnd_589082 < baseStart_589082 := by decide
  rcases family_descends (prefixWord ++ tailWord_589082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589113 : List Nat := [1, 2, 1, 6, 2, 2, 1, 1, 5]
def baseStart_589113 : Nat := 118140960795 + 589113 * 2 ^ 59
def prefixEnd_589113 : Nat := 4983230072969 + 3 ^ 40 * 589113 * 2
def baseEnd_589113 : Nat := 134443612805448367279211

theorem tailTrace_589113 : CollatzResearch.WordTrace tailWord_589113 prefixEnd_589113 134443612805448367279211 := by
  unfold tailWord_589113
  simp only [CollatzResearch.WordTrace]
  refine ⟨21486716314751688335339993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14324477543167792223559995 21486716314751688335339993)
  ·
    refine ⟨16115037236063766251504995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21486716314751688335339993 16115037236063766251504995)
    ·
      refine ⟨24172555854095649377257493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16115037236063766251504995 24172555854095649377257493)
      ·
        refine ⟨1133088555660733564558945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 24172555854095649377257493 1133088555660733564558945)
        ·
          refine ⟨849816416745550173419209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1133088555660733564558945 849816416745550173419209)
          ·
            refine ⟨637362312559162630064407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 849816416745550173419209 637362312559162630064407)
            ·
              refine ⟨956043468838743945096611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 637362312559162630064407 956043468838743945096611)
              ·
                refine ⟨1434065203258115917644917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 956043468838743945096611 1434065203258115917644917)
                ·
                  refine ⟨134443612805448367279211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1434065203258115917644917 134443612805448367279211)
                  ·
                    rfl

theorem cell21_589113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 1, 5].length) (baseStart_589113 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_589113 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_589113 prefixEnd_589113 := by exact prefixLift 589113
  have htrace : WordTrace (prefixWord ++ tailWord_589113) baseStart_589113 baseEnd_589113 := by
    simpa [prefixWord, tailWord_589113, baseEnd_589113] using wordTrace_append hprefix tailTrace_589113
  have hstable : (prefixWord ++ tailWord_589113).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589113).length < 2 ^ (prefixWord ++ tailWord_589113).sum := by decide
  have hdescent : baseEnd_589113 < baseStart_589113 := by decide
  rcases family_descends (prefixWord ++ tailWord_589113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589127 : List Nat := [1, 1, 4, 1, 2, 3, 4, 1, 4]
def baseStart_589127 : Nat := 118140960795 + 589127 * 2 ^ 59
def prefixEnd_589127 : Nat := 4983230072969 + 3 ^ 40 * 589127 * 2
def baseEnd_589127 : Nat := 134446807796187454045849

theorem tailTrace_589127 : CollatzResearch.WordTrace tailWord_589127 prefixEnd_589127 134446807796187454045849 := by
  unfold tailWord_589127
  simp only [CollatzResearch.WordTrace]
  refine ⟨21487226936700968726349635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14324817957800645817566423 21487226936700968726349635)
  ·
    refine ⟨32230840405051453089524453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21487226936700968726349635 32230840405051453089524453)
    ·
      refine ⟨6043282575947147454285835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32230840405051453089524453 6043282575947147454285835)
      ·
        refine ⟨9064923863920721181428753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6043282575947147454285835 9064923863920721181428753)
        ·
          refine ⟨6798692897940540886071565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9064923863920721181428753 6798692897940540886071565)
          ·
            refine ⟨2549509836727702832276837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6798692897940540886071565 2549509836727702832276837)
            ·
              refine ⟨478033094386444281051907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2549509836727702832276837 478033094386444281051907)
              ·
                refine ⟨717049641579666421577861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 478033094386444281051907 717049641579666421577861)
                ·
                  refine ⟨134446807796187454045849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 717049641579666421577861 134446807796187454045849)
                  ·
                    rfl

theorem cell21_589127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 1, 4].length) (baseStart_589127 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_589127 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_589127 prefixEnd_589127 := by exact prefixLift 589127
  have htrace : WordTrace (prefixWord ++ tailWord_589127) baseStart_589127 baseEnd_589127 := by
    simpa [prefixWord, tailWord_589127, baseEnd_589127] using wordTrace_append hprefix tailTrace_589127
  have hstable : (prefixWord ++ tailWord_589127).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589127).length < 2 ^ (prefixWord ++ tailWord_589127).sum := by decide
  have hdescent : baseEnd_589127 < baseStart_589127 := by decide
  rcases family_descends (prefixWord ++ tailWord_589127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589169 : List Nat := [1, 2, 2, 2, 1, 2, 2, 3, 6]
def baseStart_589169 : Nat := 118140960795 + 589169 * 2 ^ 59
def prefixEnd_589169 : Nat := 4983230072969 + 3 ^ 40 * 589169 * 2
def baseEnd_589169 : Nat := 134456392768404714345763

theorem tailTrace_589169 : CollatzResearch.WordTrace tailWord_589169 prefixEnd_589169 134456392768404714345763 := by
  unfold tailWord_589169
  simp only [CollatzResearch.WordTrace]
  refine ⟨21488758802548809899378561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14325839201699206599585707 21488758802548809899378561)
  ·
    refine ⟨16116569101911607424533921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21488758802548809899378561 16116569101911607424533921)
    ·
      refine ⟨12087426826433705568400441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16116569101911607424533921 12087426826433705568400441)
      ·
        refine ⟨9065570119825279176300331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12087426826433705568400441 9065570119825279176300331)
        ·
          refine ⟨13598355179737918764450497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9065570119825279176300331 13598355179737918764450497)
          ·
            refine ⟨10198766384803439073337873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13598355179737918764450497 10198766384803439073337873)
            ·
              refine ⟨7649074788602579305003405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10198766384803439073337873 7649074788602579305003405)
              ·
                refine ⟨2868403045725967239376277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7649074788602579305003405 2868403045725967239376277)
                ·
                  refine ⟨134456392768404714345763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2868403045725967239376277 134456392768404714345763)
                  ·
                    rfl

theorem cell21_589169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 6].length) (baseStart_589169 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_589169 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_589169 prefixEnd_589169 := by exact prefixLift 589169
  have htrace : WordTrace (prefixWord ++ tailWord_589169) baseStart_589169 baseEnd_589169 := by
    simpa [prefixWord, tailWord_589169, baseEnd_589169] using wordTrace_append hprefix tailTrace_589169
  have hstable : (prefixWord ++ tailWord_589169).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589169).length < 2 ^ (prefixWord ++ tailWord_589169).sum := by decide
  have hdescent : baseEnd_589169 < baseStart_589169 := by decide
  rcases family_descends (prefixWord ++ tailWord_589169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589335 : List Nat := [1, 1, 3, 16]
def baseStart_589335 : Nat := 118140960795 + 589335 * 2 ^ 59
def prefixEnd_589335 : Nat := 4983230072969 + 3 ^ 40 * 589335 * 2
def baseEnd_589335 : Nat := 553474387777881952999

theorem tailTrace_589335 : CollatzResearch.WordTrace tailWord_589335 prefixEnd_589335 553474387777881952999 := by
  unfold tailWord_589335
  simp only [CollatzResearch.WordTrace]
  refine ⟨21494813319947420249921459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14329875546631613499947639 21494813319947420249921459)
  ·
    refine ⟨32242219979921130374882189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21494813319947420249921459 32242219979921130374882189)
    ·
      refine ⟨12090832492470423890580821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32242219979921130374882189 12090832492470423890580821)
      ·
        refine ⟨553474387777881952999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 16 12090832492470423890580821 553474387777881952999)
        ·
          rfl

theorem cell21_589335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 16].length) (baseStart_589335 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_589335 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_589335 prefixEnd_589335 := by exact prefixLift 589335
  have htrace : WordTrace (prefixWord ++ tailWord_589335) baseStart_589335 baseEnd_589335 := by
    simpa [prefixWord, tailWord_589335, baseEnd_589335] using wordTrace_append hprefix tailTrace_589335
  have hstable : (prefixWord ++ tailWord_589335).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589335).length < 2 ^ (prefixWord ++ tailWord_589335).sum := by decide
  have hdescent : baseEnd_589335 < baseStart_589335 := by decide
  rcases family_descends (prefixWord ++ tailWord_589335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589369 : List Nat := [1, 2, 1, 5, 1, 3, 3, 5]
def baseStart_589369 : Nat := 118140960795 + 589369 * 2 ^ 59
def prefixEnd_589369 : Nat := 4983230072969 + 3 ^ 40 * 589369 * 2
def baseEnd_589369 : Nat := 44834011831082937004007

theorem tailTrace_589369 : CollatzResearch.WordTrace tailWord_589369 prefixEnd_589369 44834011831082937004007 := by
  unfold tailWord_589369
  simp only [CollatzResearch.WordTrace]
  refine ⟨21496053401824244056659161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14330702267882829371106107 21496053401824244056659161)
  ·
    refine ⟨16122040051368183042494371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21496053401824244056659161 16122040051368183042494371)
    ·
      refine ⟨24183060077052274563741557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16122040051368183042494371 24183060077052274563741557)
      ·
        refine ⟨2267161882223650740350771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24183060077052274563741557 2267161882223650740350771)
        ·
          refine ⟨3400742823335476110526157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2267161882223650740350771 3400742823335476110526157)
          ·
            refine ⟨1275278558750803541447309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3400742823335476110526157 1275278558750803541447309)
            ·
              refine ⟨478229459531551328042741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1275278558750803541447309 478229459531551328042741)
              ·
                refine ⟨44834011831082937004007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 478229459531551328042741 44834011831082937004007)
                ·
                  rfl

theorem cell21_589369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 5].length) (baseStart_589369 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_589369 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_589369 prefixEnd_589369 := by exact prefixLift 589369
  have htrace : WordTrace (prefixWord ++ tailWord_589369) baseStart_589369 baseEnd_589369 := by
    simpa [prefixWord, tailWord_589369, baseEnd_589369] using wordTrace_append hprefix tailTrace_589369
  have hstable : (prefixWord ++ tailWord_589369).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589369).length < 2 ^ (prefixWord ++ tailWord_589369).sum := by decide
  have hdescent : baseEnd_589369 < baseStart_589369 := by decide
  rcases family_descends (prefixWord ++ tailWord_589369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589389 : List Nat := [1, 6, 1, 1, 4, 1, 1, 2, 4]
def baseStart_589389 : Nat := 118140960795 + 589389 * 2 ^ 59
def prefixEnd_589389 : Nat := 4983230072969 + 3 ^ 40 * 589389 * 2
def baseEnd_589389 : Nat := 134506599765733220678647

theorem tailTrace_589389 : CollatzResearch.WordTrace tailWord_589389 prefixEnd_589389 134506599765733220678647 := by
  unfold tailWord_589389
  simp only [CollatzResearch.WordTrace]
  refine ⟨21496782861751787472387221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14331188574501191648258147 21496782861751787472387221)
  ·
    refine ⟨1007661696644615037768151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 21496782861751787472387221 1007661696644615037768151)
    ·
      refine ⟨1511492544966922556652227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1007661696644615037768151 1511492544966922556652227)
      ·
        refine ⟨2267238817450383834978341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1511492544966922556652227 2267238817450383834978341)
        ·
          refine ⟨425107278271946969058439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2267238817450383834978341 425107278271946969058439)
          ·
            refine ⟨637660917407920453587659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 425107278271946969058439 637660917407920453587659)
            ·
              refine ⟨956491376111880680381489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 637660917407920453587659 956491376111880680381489)
              ·
                refine ⟨717368532083910510286117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 956491376111880680381489 717368532083910510286117)
                ·
                  refine ⟨134506599765733220678647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 717368532083910510286117 134506599765733220678647)
                  ·
                    rfl

theorem cell21_589389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_589389 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_589389 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_589389 prefixEnd_589389 := by exact prefixLift 589389
  have htrace : WordTrace (prefixWord ++ tailWord_589389) baseStart_589389 baseEnd_589389 := by
    simpa [prefixWord, tailWord_589389, baseEnd_589389] using wordTrace_append hprefix tailTrace_589389
  have hstable : (prefixWord ++ tailWord_589389).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589389).length < 2 ^ (prefixWord ++ tailWord_589389).sum := by decide
  have hdescent : baseEnd_589389 < baseStart_589389 := by decide
  rcases family_descends (prefixWord ++ tailWord_589389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589487 : List Nat := [1, 1, 2, 1, 2, 4, 1, 9]
def baseStart_589487 : Nat := 118140960795 + 589487 * 2 ^ 59
def prefixEnd_589487 : Nat := 4983230072969 + 3 ^ 40 * 589487 * 2
def baseEnd_589487 : Nat := 44842988233635609348371

theorem tailTrace_589487 : CollatzResearch.WordTrace tailWord_589487 prefixEnd_589487 44842988233635609348371 := by
  unfold tailWord_589487
  simp only [CollatzResearch.WordTrace]
  refine ⟨21500357215396750209454715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14333571476931166806303143 21500357215396750209454715)
  ·
    refine ⟨32250535823095125314182073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21500357215396750209454715 32250535823095125314182073)
    ·
      refine ⟨24187901867321343985636555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32250535823095125314182073 24187901867321343985636555)
      ·
        refine ⟨36281852800982015978454833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24187901867321343985636555 36281852800982015978454833)
        ·
          refine ⟨27211389600736511983841125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36281852800982015978454833 27211389600736511983841125)
          ·
            refine ⟨5102135550138095996970211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27211389600736511983841125 5102135550138095996970211)
            ·
              refine ⟨7653203325207143995455317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5102135550138095996970211 7653203325207143995455317)
              ·
                refine ⟨44842988233635609348371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7653203325207143995455317 44842988233635609348371)
                ·
                  rfl

theorem cell21_589487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 9].length) (baseStart_589487 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_589487 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_589487 prefixEnd_589487 := by exact prefixLift 589487
  have htrace : WordTrace (prefixWord ++ tailWord_589487) baseStart_589487 baseEnd_589487 := by
    simpa [prefixWord, tailWord_589487, baseEnd_589487] using wordTrace_append hprefix tailTrace_589487
  have hstable : (prefixWord ++ tailWord_589487).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589487).length < 2 ^ (prefixWord ++ tailWord_589487).sum := by decide
  have hdescent : baseEnd_589487 < baseStart_589487 := by decide
  rcases family_descends (prefixWord ++ tailWord_589487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589614 : List Nat := [4, 1, 3, 2, 3, 1, 7]
def baseStart_589614 : Nat := 118140960795 + 589614 * 2 ^ 59
def prefixEnd_589614 : Nat := 4983230072969 + 3 ^ 40 * 589614 * 2
def baseEnd_589614 : Nat := 14950883092353647714243

theorem tailTrace_589614 : CollatzResearch.WordTrace tailWord_589614 prefixEnd_589614 14950883092353647714243 := by
  unfold tailWord_589614
  simp only [CollatzResearch.WordTrace]
  refine ⟨2688123660742081362415987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14336659523957767266218597 2688123660742081362415987)
  ·
    refine ⟨4032185491113122043623981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2688123660742081362415987 4032185491113122043623981)
    ·
      refine ⟨1512069559167420766358993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4032185491113122043623981 1512069559167420766358993)
      ·
        refine ⟨1134052169375565574769245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1512069559167420766358993 1134052169375565574769245)
        ·
          refine ⟨425269563515837090538467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1134052169375565574769245 425269563515837090538467)
          ·
            refine ⟨637904345273755635807701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 425269563515837090538467 637904345273755635807701)
            ·
              refine ⟨14950883092353647714243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 637904345273755635807701 14950883092353647714243)
              ·
                rfl

theorem cell21_589614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 7].length) (baseStart_589614 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_589614 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_589614 prefixEnd_589614 := by exact prefixLift 589614
  have htrace : WordTrace (prefixWord ++ tailWord_589614) baseStart_589614 baseEnd_589614 := by
    simpa [prefixWord, tailWord_589614, baseEnd_589614] using wordTrace_append hprefix tailTrace_589614
  have hstable : (prefixWord ++ tailWord_589614).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589614).length < 2 ^ (prefixWord ++ tailWord_589614).sum := by decide
  have hdescent : baseEnd_589614 < baseStart_589614 := by decide
  rcases family_descends (prefixWord ++ tailWord_589614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589639 : List Nat := [1, 1, 4, 1, 2, 1, 3, 8]
def baseStart_589639 : Nat := 118140960795 + 589639 * 2 ^ 59
def prefixEnd_589639 : Nat := 4983230072969 + 3 ^ 40 * 589639 * 2
def baseEnd_589639 : Nat := 44854551057262780503823

theorem tailTrace_589639 : CollatzResearch.WordTrace tailWord_589639 prefixEnd_589639 44854551057262780503823 := by
  unfold tailWord_589639
  simp only [CollatzResearch.WordTrace]
  refine ⟨21505901110846080168987971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14337267407230720112658647 21505901110846080168987971)
  ·
    refine ⟨32258851666269120253481957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21505901110846080168987971 32258851666269120253481957)
    ·
      refine ⟨6048534687425460047527867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32258851666269120253481957 6048534687425460047527867)
      ·
        refine ⟨9072802031138190071291801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6048534687425460047527867 9072802031138190071291801)
        ·
          refine ⟨6804601523353642553468851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9072802031138190071291801 6804601523353642553468851)
          ·
            refine ⟨10206902285030463830203277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6804601523353642553468851 10206902285030463830203277)
            ·
              refine ⟨3827588356886423936326229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10206902285030463830203277 3827588356886423936326229)
              ·
                refine ⟨44854551057262780503823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3827588356886423936326229 44854551057262780503823)
                ·
                  rfl

theorem cell21_589639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 8].length) (baseStart_589639 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_589639 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_589639 prefixEnd_589639 := by exact prefixLift 589639
  have htrace : WordTrace (prefixWord ++ tailWord_589639) baseStart_589639 baseEnd_589639 := by
    simpa [prefixWord, tailWord_589639, baseEnd_589639] using wordTrace_append hprefix tailTrace_589639
  have hstable : (prefixWord ++ tailWord_589639).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589639).length < 2 ^ (prefixWord ++ tailWord_589639).sum := by decide
  have hdescent : baseEnd_589639 < baseStart_589639 := by decide
  rcases family_descends (prefixWord ++ tailWord_589639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589701 : List Nat := [1, 3, 1, 1, 3, 2, 1, 5, 4]
def baseStart_589701 : Nat := 118140960795 + 589701 * 2 ^ 59
def prefixEnd_589701 : Nat := 4983230072969 + 3 ^ 40 * 589701 * 2
def baseEnd_589701 : Nat := 134577802416490011478009

theorem tailTrace_589701 : CollatzResearch.WordTrace tailWord_589701 prefixEnd_589701 134577802416490011478009 := by
  unfold tailWord_589701
  simp only [CollatzResearch.WordTrace]
  refine ⟨21508162436621464757744957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14338774957747643171829971 21508162436621464757744957)
  ·
    refine ⟨8065560913733049284154359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21508162436621464757744957 8065560913733049284154359)
    ·
      refine ⟨12098341370599573926231539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8065560913733049284154359 12098341370599573926231539)
      ·
        refine ⟨18147512055899360889347309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12098341370599573926231539 18147512055899360889347309)
        ·
          refine ⟨6805317020962260333505241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18147512055899360889347309 6805317020962260333505241)
          ·
            refine ⟨5103987765721695250128931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6805317020962260333505241 5103987765721695250128931)
            ·
              refine ⟨7655981648582542875193397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5103987765721695250128931 7655981648582542875193397)
              ·
                refine ⟨717748279554613394549381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7655981648582542875193397 717748279554613394549381)
                ·
                  refine ⟨134577802416490011478009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 717748279554613394549381 134577802416490011478009)
                  ·
                    rfl

theorem cell21_589701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 5, 4].length) (baseStart_589701 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_589701 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_589701 prefixEnd_589701 := by exact prefixLift 589701
  have htrace : WordTrace (prefixWord ++ tailWord_589701) baseStart_589701 baseEnd_589701 := by
    simpa [prefixWord, tailWord_589701, baseEnd_589701] using wordTrace_append hprefix tailTrace_589701
  have hstable : (prefixWord ++ tailWord_589701).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589701).length < 2 ^ (prefixWord ++ tailWord_589701).sum := by decide
  have hdescent : baseEnd_589701 < baseStart_589701 := by decide
  rcases family_descends (prefixWord ++ tailWord_589701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589735 : List Nat := [1, 1, 6, 1, 2, 3, 1, 2, 4]
def baseStart_589735 : Nat := 118140960795 + 589735 * 2 ^ 59
def prefixEnd_589735 : Nat := 4983230072969 + 3 ^ 40 * 589735 * 2
def baseEnd_589735 : Nat := 134585561679713507911273

theorem tailTrace_589735 : CollatzResearch.WordTrace tailWord_589735 prefixEnd_589735 134585561679713507911273 := by
  unfold tailWord_589735
  simp only [CollatzResearch.WordTrace]
  refine ⟨21509402518498288564482659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14339601678998859042988439 21509402518498288564482659)
  ·
    refine ⟨32264103777747432846723989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21509402518498288564482659 32264103777747432846723989)
    ·
      refine ⟨1512379864581910914690187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 32264103777747432846723989 1512379864581910914690187)
      ·
        refine ⟨2268569796872866372035281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1512379864581910914690187 2268569796872866372035281)
        ·
          refine ⟨1701427347654649779026461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2268569796872866372035281 1701427347654649779026461)
          ·
            refine ⟨638035255370493667134923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1701427347654649779026461 638035255370493667134923)
            ·
              refine ⟨957052883055740500702385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 638035255370493667134923 957052883055740500702385)
              ·
                refine ⟨717789662291805375526789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 957052883055740500702385 717789662291805375526789)
                ·
                  refine ⟨134585561679713507911273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 717789662291805375526789 134585561679713507911273)
                  ·
                    rfl

theorem cell21_589735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 2, 4].length) (baseStart_589735 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_589735 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_589735 prefixEnd_589735 := by exact prefixLift 589735
  have htrace : WordTrace (prefixWord ++ tailWord_589735) baseStart_589735 baseEnd_589735 := by
    simpa [prefixWord, tailWord_589735, baseEnd_589735] using wordTrace_append hprefix tailTrace_589735
  have hstable : (prefixWord ++ tailWord_589735).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589735).length < 2 ^ (prefixWord ++ tailWord_589735).sum := by decide
  have hdescent : baseEnd_589735 < baseStart_589735 := by decide
  rcases family_descends (prefixWord ++ tailWord_589735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589791 : List Nat := [1, 1, 2, 3, 4, 1, 9]
def baseStart_589791 : Nat := 118140960795 + 589791 * 2 ^ 59
def prefixEnd_589791 : Nat := 4983230072969 + 3 ^ 40 * 589791 * 2
def baseEnd_589791 : Nat := 14955371293629983886425

theorem tailTrace_589791 : CollatzResearch.WordTrace tailWord_589791 prefixEnd_589791 14955371293629983886425 := by
  unfold tailWord_589791
  simp only [CollatzResearch.WordTrace]
  refine ⟨21511445006295410128521227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14340963337530273419014151 21511445006295410128521227)
  ·
    refine ⟨32267167509443115192781841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21511445006295410128521227 32267167509443115192781841)
    ·
      refine ⟨24200375632082336394586381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32267167509443115192781841 24200375632082336394586381)
      ·
        refine ⟨9075140862030876147969893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24200375632082336394586381 9075140862030876147969893)
        ·
          refine ⟨1701588911630789277744355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9075140862030876147969893 1701588911630789277744355)
          ·
            refine ⟨2552383367446183916616533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1701588911630789277744355 2552383367446183916616533)
            ·
              refine ⟨14955371293629983886425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2552383367446183916616533 14955371293629983886425)
              ·
                rfl

theorem cell21_589791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 9].length) (baseStart_589791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_589791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_589791 prefixEnd_589791 := by exact prefixLift 589791
  have htrace : WordTrace (prefixWord ++ tailWord_589791) baseStart_589791 baseEnd_589791 := by
    simpa [prefixWord, tailWord_589791, baseEnd_589791] using wordTrace_append hprefix tailTrace_589791
  have hstable : (prefixWord ++ tailWord_589791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589791).length < 2 ^ (prefixWord ++ tailWord_589791).sum := by decide
  have hdescent : baseEnd_589791 < baseStart_589791 := by decide
  rcases family_descends (prefixWord ++ tailWord_589791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589870 : List Nat := [4, 1, 3, 1, 1, 2, 2, 3, 4]
def baseStart_589870 : Nat := 118140960795 + 589870 * 2 ^ 59
def prefixEnd_589870 : Nat := 4983230072969 + 3 ^ 40 * 589870 * 2
def baseEnd_589870 : Nat := 134616370518983273160997

theorem tailTrace_589870 : CollatzResearch.WordTrace tailWord_589870 prefixEnd_589870 134616370518983273160997 := by
  unfold tailWord_589870
  simp only [CollatzResearch.WordTrace]
  refine ⟨2689290796626150827580883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14342884248672804413764709 2689290796626150827580883)
  ·
    refine ⟨4033936194939226241371325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2689290796626150827580883 4033936194939226241371325)
    ·
      refine ⟨1512726073102209840514247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4033936194939226241371325 1512726073102209840514247)
      ·
        refine ⟨2269089109653314760771371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1512726073102209840514247 2269089109653314760771371)
        ·
          refine ⟨3403633664479972141157057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2269089109653314760771371 3403633664479972141157057)
          ·
            refine ⟨2552725248359979105867793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3403633664479972141157057 2552725248359979105867793)
            ·
              refine ⟨1914543936269984329400845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2552725248359979105867793 1914543936269984329400845)
              ·
                refine ⟨717953976101244123525317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1914543936269984329400845 717953976101244123525317)
                ·
                  refine ⟨134616370518983273160997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 717953976101244123525317 134616370518983273160997)
                  ·
                    rfl

theorem cell21_589870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_589870 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_589870 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_589870 prefixEnd_589870 := by exact prefixLift 589870
  have htrace : WordTrace (prefixWord ++ tailWord_589870) baseStart_589870 baseEnd_589870 := by
    simpa [prefixWord, tailWord_589870, baseEnd_589870] using wordTrace_append hprefix tailTrace_589870
  have hstable : (prefixWord ++ tailWord_589870).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589870).length < 2 ^ (prefixWord ++ tailWord_589870).sum := by decide
  have hdescent : baseEnd_589870 < baseStart_589870 := by decide
  rcases family_descends (prefixWord ++ tailWord_589870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589884 : List Nat := [2, 2, 2, 2, 2, 1, 5, 5]
def baseStart_589884 : Nat := 118140960795 + 589884 * 2 ^ 59
def prefixEnd_589884 : Nat := 4983230072969 + 3 ^ 40 * 589884 * 2
def baseEnd_589884 : Nat := 44873188503240786642545

theorem tailTrace_589884 : CollatzResearch.WordTrace tailWord_589884 prefixEnd_589884 44873188503240786642545 := by
  unfold tailWord_589884
  simp only [CollatzResearch.WordTrace]
  refine ⟨10757418497479243505828353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14343224663305658007771137 10757418497479243505828353)
  ·
    refine ⟨8068063873109432629371265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10757418497479243505828353 8068063873109432629371265)
    ·
      refine ⟨6051047904832074472028449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8068063873109432629371265 6051047904832074472028449)
      ·
        refine ⟨4538285928624055854021337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6051047904832074472028449 4538285928624055854021337)
        ·
          refine ⟨3403714446468041890516003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4538285928624055854021337 3403714446468041890516003)
          ·
            refine ⟨5105571669702062835774005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3403714446468041890516003 5105571669702062835774005)
            ·
              refine ⟨478647344034568390853813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5105571669702062835774005 478647344034568390853813)
              ·
                refine ⟨44873188503240786642545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 478647344034568390853813 44873188503240786642545)
                ·
                  rfl

theorem cell21_589884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 5].length) (baseStart_589884 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_589884 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_589884 prefixEnd_589884 := by exact prefixLift 589884
  have htrace : WordTrace (prefixWord ++ tailWord_589884) baseStart_589884 baseEnd_589884 := by
    simpa [prefixWord, tailWord_589884, baseEnd_589884] using wordTrace_append hprefix tailTrace_589884
  have hstable : (prefixWord ++ tailWord_589884).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589884).length < 2 ^ (prefixWord ++ tailWord_589884).sum := by decide
  have hdescent : baseEnd_589884 < baseStart_589884 := by decide
  rcases family_descends (prefixWord ++ tailWord_589884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589943 : List Nat := [1, 1, 3, 1, 1, 6, 1, 7]
def baseStart_589943 : Nat := 118140960795 + 589943 * 2 ^ 59
def prefixEnd_589943 : Nat := 4983230072969 + 3 ^ 40 * 589943 * 2
def baseEnd_589943 : Nat := 44877676704517122814727

theorem tailTrace_589943 : CollatzResearch.WordTrace tailWord_589943 prefixEnd_589943 44877676704517122814727 := by
  unfold tailWord_589943
  simp only [CollatzResearch.WordTrace]
  refine ⟨21516988901744740088054483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14344659267829826725369655 21516988901744740088054483)
  ·
    refine ⟨32275483352617110132081725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21516988901744740088054483 32275483352617110132081725)
    ·
      refine ⟨12103306257231416299530647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32275483352617110132081725 12103306257231416299530647)
      ·
        refine ⟨18154959385847124449295971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12103306257231416299530647 18154959385847124449295971)
        ·
          refine ⟨27232439078770686673943957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18154959385847124449295971 27232439078770686673943957)
          ·
            refine ⟨1276520581817375937841123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 27232439078770686673943957 1276520581817375937841123)
            ·
              refine ⟨1914780872726063906761685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1276520581817375937841123 1914780872726063906761685)
              ·
                refine ⟨44877676704517122814727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1914780872726063906761685 44877676704517122814727)
                ·
                  rfl

theorem cell21_589943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 7].length) (baseStart_589943 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_589943 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_589943 prefixEnd_589943 := by exact prefixLift 589943
  have htrace : WordTrace (prefixWord ++ tailWord_589943) baseStart_589943 baseEnd_589943 := by
    simpa [prefixWord, tailWord_589943, baseEnd_589943] using wordTrace_append hprefix tailTrace_589943
  have hstable : (prefixWord ++ tailWord_589943).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589943).length < 2 ^ (prefixWord ++ tailWord_589943).sum := by decide
  have hdescent : baseEnd_589943 < baseStart_589943 := by decide
  rcases family_descends (prefixWord ++ tailWord_589943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589960 : List Nat := [2, 1, 3, 4, 1, 3, 7]
def baseStart_589960 : Nat := 118140960795 + 589960 * 2 ^ 59
def prefixEnd_589960 : Nat := 4983230072969 + 3 ^ 40 * 589960 * 2
def baseEnd_589960 : Nat := 14959656638351457406757

theorem tailTrace_589960 : CollatzResearch.WordTrace tailWord_589960 prefixEnd_589960 14959656638351457406757 := by
  unfold tailWord_589960
  simp only [CollatzResearch.WordTrace]
  refine ⟨10758804471341575995711667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14345072628455434660948889 10758804471341575995711667)
  ·
    refine ⟨16138206707012363993567501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10758804471341575995711667 16138206707012363993567501)
    ·
      refine ⟨6051827515129636497587813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16138206707012363993567501 6051827515129636497587813)
      ·
        refine ⟨1134717659086806843297715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6051827515129636497587813 1134717659086806843297715)
        ·
          refine ⟨1702076488630210264946573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1134717659086806843297715 1702076488630210264946573)
          ·
            refine ⟨638278683236328849354965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1702076488630210264946573 638278683236328849354965)
            ·
              refine ⟨14959656638351457406757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 638278683236328849354965 14959656638351457406757)
              ·
                rfl

theorem cell21_589960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 7].length) (baseStart_589960 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_589960 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_589960 prefixEnd_589960 := by exact prefixLift 589960
  have htrace : WordTrace (prefixWord ++ tailWord_589960) baseStart_589960 baseEnd_589960 := by
    simpa [prefixWord, tailWord_589960, baseEnd_589960] using wordTrace_append hprefix tailTrace_589960
  have hstable : (prefixWord ++ tailWord_589960).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589960).length < 2 ^ (prefixWord ++ tailWord_589960).sum := by decide
  have hdescent : baseEnd_589960 < baseStart_589960 := by decide
  rcases family_descends (prefixWord ++ tailWord_589960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590067 : List Nat := [1, 1, 1, 2, 2, 4, 4, 3, 3]
def baseStart_590067 : Nat := 118140960795 + 590067 * 2 ^ 59
def prefixEnd_590067 : Nat := 4983230072969 + 3 ^ 40 * 590067 * 2
def baseEnd_590067 : Nat := 134661328602954708377261

theorem tailTrace_590067 : CollatzResearch.WordTrace tailWord_590067 prefixEnd_590067 134661328602954708377261 := by
  unfold tailWord_590067
  simp only [CollatzResearch.WordTrace]
  refine ⟨21521511553295509265568455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14347674368863672843712303 21521511553295509265568455)
  ·
    refine ⟨32282267329943263898352683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21521511553295509265568455 32282267329943263898352683)
    ·
      refine ⟨48423400994914895847529025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32282267329943263898352683 48423400994914895847529025)
      ·
        refine ⟨36317550746186171885646769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48423400994914895847529025 36317550746186171885646769)
        ·
          refine ⟨27238163059639628914235077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36317550746186171885646769 27238163059639628914235077)
          ·
            refine ⟨5107155573682430421419077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27238163059639628914235077 5107155573682430421419077)
            ·
              refine ⟨957591670065455704016077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5107155573682430421419077 957591670065455704016077)
              ·
                refine ⟨359096876274545889006029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 957591670065455704016077 359096876274545889006029)
                ·
                  refine ⟨134661328602954708377261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 359096876274545889006029 134661328602954708377261)
                  ·
                    rfl

theorem cell21_590067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 3, 3].length) (baseStart_590067 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_590067 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_590067 prefixEnd_590067 := by exact prefixLift 590067
  have htrace : WordTrace (prefixWord ++ tailWord_590067) baseStart_590067 baseEnd_590067 := by
    simpa [prefixWord, tailWord_590067, baseEnd_590067] using wordTrace_append hprefix tailTrace_590067
  have hstable : (prefixWord ++ tailWord_590067).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590067).length < 2 ^ (prefixWord ++ tailWord_590067).sum := by decide
  have hdescent : baseEnd_590067 < baseStart_590067 := by decide
  rcases family_descends (prefixWord ++ tailWord_590067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590112 : List Nat := [2, 1, 1, 5, 2, 1, 4, 5]
def baseStart_590112 : Nat := 118140960795 + 590112 * 2 ^ 59
def prefixEnd_590112 : Nat := 4983230072969 + 3 ^ 40 * 590112 * 2
def baseEnd_590112 : Nat := 44890532738681543375723

theorem tailTrace_590112 : CollatzResearch.WordTrace tailWord_590112 prefixEnd_590112 44890532738681543375723 := by
  unfold tailWord_590112
  simp only [CollatzResearch.WordTrace]
  refine ⟨10761576419066240975478295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14348768558754987967304393 10761576419066240975478295)
  ·
    refine ⟨16142364628599361463217443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10761576419066240975478295 16142364628599361463217443)
    ·
      refine ⟨24213546942899042194826165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16142364628599361463217443 24213546942899042194826165)
      ·
        refine ⟨2270020025896785205764953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24213546942899042194826165 2270020025896785205764953)
        ·
          refine ⟨1702515019422588904323715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2270020025896785205764953 1702515019422588904323715)
          ·
            refine ⟨2553772529133883356485573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1702515019422588904323715 2553772529133883356485573)
            ·
              refine ⟨478832349212603129341045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2553772529133883356485573 478832349212603129341045)
              ·
                refine ⟨44890532738681543375723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 478832349212603129341045 44890532738681543375723)
                ·
                  rfl

theorem cell21_590112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 5].length) (baseStart_590112 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_590112 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_590112 prefixEnd_590112 := by exact prefixLift 590112
  have htrace : WordTrace (prefixWord ++ tailWord_590112) baseStart_590112 baseEnd_590112 := by
    simpa [prefixWord, tailWord_590112, baseEnd_590112] using wordTrace_append hprefix tailTrace_590112
  have hstable : (prefixWord ++ tailWord_590112).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590112).length < 2 ^ (prefixWord ++ tailWord_590112).sum := by decide
  have hdescent : baseEnd_590112 < baseStart_590112 := by decide
  rcases family_descends (prefixWord ++ tailWord_590112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590140 : List Nat := [2, 2, 2, 2, 1, 2, 1, 3, 6]
def baseStart_590140 : Nat := 118140960795 + 590140 * 2 ^ 59
def prefixEnd_590140 : Nat := 4983230072969 + 3 ^ 40 * 590140 * 2
def baseEnd_590140 : Nat := 134677988197522803660445

theorem tailTrace_590140 : CollatzResearch.WordTrace tailWord_590140 prefixEnd_590140 134677988197522803660445 := by
  unfold tailWord_590140
  simp only [CollatzResearch.WordTrace]
  refine ⟨10762087041015521366487937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14349449388020695155317249 10762087041015521366487937)
  ·
    refine ⟨8071565280761641024865953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10762087041015521366487937 8071565280761641024865953)
    ·
      refine ⟨6053673960571230768649465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8071565280761641024865953 6053673960571230768649465)
      ·
        refine ⟨4540255470428423076487099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6053673960571230768649465 4540255470428423076487099)
        ·
          refine ⟨6810383205642634614730649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4540255470428423076487099 6810383205642634614730649)
          ·
            refine ⟨5107787404231975961047987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6810383205642634614730649 5107787404231975961047987)
            ·
              refine ⟨7661681106347963941571981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5107787404231975961047987 7661681106347963941571981)
              ·
                refine ⟨2873130414880486478089493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7661681106347963941571981 2873130414880486478089493)
                ·
                  refine ⟨134677988197522803660445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2873130414880486478089493 134677988197522803660445)
                  ·
                    rfl

theorem cell21_590140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 6].length) (baseStart_590140 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_590140 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_590140 prefixEnd_590140 := by exact prefixLift 590140
  have htrace : WordTrace (prefixWord ++ tailWord_590140) baseStart_590140 baseEnd_590140 := by
    simpa [prefixWord, tailWord_590140, baseEnd_590140] using wordTrace_append hprefix tailTrace_590140
  have hstable : (prefixWord ++ tailWord_590140).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590140).length < 2 ^ (prefixWord ++ tailWord_590140).sum := by decide
  have hdescent : baseEnd_590140 < baseStart_590140 := by decide
  rcases family_descends (prefixWord ++ tailWord_590140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590247 : List Nat := [1, 1, 6, 1, 1, 3, 8]
def baseStart_590247 : Nat := 118140960795 + 590247 * 2 ^ 59
def prefixEnd_590247 : Nat := 4983230072969 + 3 ^ 40 * 590247 * 2
def baseEnd_590247 : Nat := 14966934117257155041877

theorem tailTrace_590247 : CollatzResearch.WordTrace tailWord_590247 prefixEnd_590247 14966934117257155041877 := by
  unfold tailWord_590247
  simp only [CollatzResearch.WordTrace]
  refine ⟨21528076692643400007120995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14352051128428933338080663 21528076692643400007120995)
  ·
    refine ⟨32292115038965100010681493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21528076692643400007120995 32292115038965100010681493)
    ·
      refine ⟨1513692892451489063000695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 32292115038965100010681493 1513692892451489063000695)
      ·
        refine ⟨2270539338677233594501043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1513692892451489063000695 2270539338677233594501043)
        ·
          refine ⟨3405809008015850391751565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2270539338677233594501043 3405809008015850391751565)
          ·
            refine ⟨1277178378005943896906837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3405809008015850391751565 1277178378005943896906837)
            ·
              refine ⟨14966934117257155041877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1277178378005943896906837 14966934117257155041877)
              ·
                rfl

theorem cell21_590247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 8].length) (baseStart_590247 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_590247 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_590247 prefixEnd_590247 := by exact prefixLift 590247
  have htrace : WordTrace (prefixWord ++ tailWord_590247) baseStart_590247 baseEnd_590247 := by
    simpa [prefixWord, tailWord_590247, baseEnd_590247] using wordTrace_append hprefix tailTrace_590247
  have hstable : (prefixWord ++ tailWord_590247).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590247).length < 2 ^ (prefixWord ++ tailWord_590247).sum := by decide
  have hdescent : baseEnd_590247 < baseStart_590247 := by decide
  rcases family_descends (prefixWord ++ tailWord_590247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590312 : List Nat := [2, 1, 4, 1, 1, 4, 3, 2, 3]
def baseStart_590312 : Nat := 118140960795 + 590312 * 2 ^ 59
def prefixEnd_590312 : Nat := 4983230072969 + 3 ^ 40 * 590312 * 2
def baseEnd_590312 : Nat := 134717240940888726793427

theorem tailTrace_590312 : CollatzResearch.WordTrace tailWord_590312 prefixEnd_590312 134717240940888726793427 := by
  unfold tailWord_590312
  simp only [CollatzResearch.WordTrace]
  refine ⟨10765223718703958054118595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14353631624938610738824793 10765223718703958054118595)
  ·
    refine ⟨16147835578055937081177893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10765223718703958054118595 16147835578055937081177893)
    ·
      refine ⟨3027719170885488202720855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16147835578055937081177893 3027719170885488202720855)
      ·
        refine ⟨4541578756328232304081283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3027719170885488202720855 4541578756328232304081283)
        ·
          refine ⟨6812368134492348456121925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4541578756328232304081283 6812368134492348456121925)
          ·
            refine ⟨1277319025217315335522861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6812368134492348456121925 1277319025217315335522861)
            ·
              refine ⟨478994634456493250821073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1277319025217315335522861 478994634456493250821073)
              ·
                refine ⟨359245975842369938115805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 478994634456493250821073 359245975842369938115805)
                ·
                  refine ⟨134717240940888726793427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 359245975842369938115805 134717240940888726793427)
                  ·
                    rfl

theorem cell21_590312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 2, 3].length) (baseStart_590312 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_590312 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_590312 prefixEnd_590312 := by exact prefixLift 590312
  have htrace : WordTrace (prefixWord ++ tailWord_590312) baseStart_590312 baseEnd_590312 := by
    simpa [prefixWord, tailWord_590312, baseEnd_590312] using wordTrace_append hprefix tailTrace_590312
  have hstable : (prefixWord ++ tailWord_590312).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590312).length < 2 ^ (prefixWord ++ tailWord_590312).sum := by decide
  have hdescent : baseEnd_590312 < baseStart_590312 := by decide
  rcases family_descends (prefixWord ++ tailWord_590312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590371 : List Nat := [1, 1, 1, 4, 4, 2, 1, 4, 3]
def baseStart_590371 : Nat := 118140960795 + 590371 * 2 ^ 59
def prefixEnd_590371 : Nat := 4983230072969 + 3 ^ 40 * 590371 * 2
def baseEnd_590371 : Nat := 134730705544717735309973

theorem tailTrace_590371 : CollatzResearch.WordTrace tailWord_590371 prefixEnd_590371 134730705544717735309973 := by
  unfold tailWord_590371
  simp only [CollatzResearch.WordTrace]
  refine ⟨21532599344194169184634967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14355066229462779456423311 21532599344194169184634967)
  ·
    refine ⟨32298899016291253776952451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21532599344194169184634967 32298899016291253776952451)
    ·
      refine ⟨48448348524436880665428677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32298899016291253776952451 48448348524436880665428677)
      ·
        refine ⟨9084065348331915124767877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48448348524436880665428677 9084065348331915124767877)
        ·
          refine ⟨1703262252812234085893977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9084065348331915124767877 1703262252812234085893977)
          ·
            refine ⟨1277446689609175564420483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1703262252812234085893977 1277446689609175564420483)
            ·
              refine ⟨1916170034413763346630725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1277446689609175564420483 1916170034413763346630725)
              ·
                refine ⟨359281881452580627493261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1916170034413763346630725 359281881452580627493261)
                ·
                  refine ⟨134730705544717735309973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 359281881452580627493261 134730705544717735309973)
                  ·
                    rfl

theorem cell21_590371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 4, 3].length) (baseStart_590371 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_590371 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_590371 prefixEnd_590371 := by exact prefixLift 590371
  have htrace : WordTrace (prefixWord ++ tailWord_590371) baseStart_590371 baseEnd_590371 := by
    simpa [prefixWord, tailWord_590371, baseEnd_590371] using wordTrace_append hprefix tailTrace_590371
  have hstable : (prefixWord ++ tailWord_590371).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590371).length < 2 ^ (prefixWord ++ tailWord_590371).sum := by decide
  have hdescent : baseEnd_590371 < baseStart_590371 := by decide
  rcases family_descends (prefixWord ++ tailWord_590371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590388 : List Nat := [2, 5, 1, 3, 1, 1, 1, 2, 5]
def baseStart_590388 : Nat := 118140960795 + 590388 * 2 ^ 59
def prefixEnd_590388 : Nat := 4983230072969 + 3 ^ 40 * 590388 * 2
def baseEnd_590388 : Nat := 134734585176329483526605

theorem tailTrace_590388 : CollatzResearch.WordTrace tailWord_590388 prefixEnd_590388 134734585176329483526605 := by
  unfold tailWord_590388
  simp only [CollatzResearch.WordTrace]
  refine ⟨10766609692566290544001909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14355479590088387392002545 10766609692566290544001909)
  ·
    refine ⟨1009369658678089738500179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10766609692566290544001909 1009369658678089738500179)
    ·
      refine ⟨1514054488017134607750269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1009369658678089738500179 1514054488017134607750269)
      ·
        refine ⟨567770433006425477906351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1514054488017134607750269 567770433006425477906351)
        ·
          refine ⟨851655649509638216859527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 567770433006425477906351 851655649509638216859527)
          ·
            refine ⟨1277483474264457325289291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 851655649509638216859527 1277483474264457325289291)
            ·
              refine ⟨1916225211396685987933937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1277483474264457325289291 1916225211396685987933937)
              ·
                refine ⟨1437168908547514490950453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1916225211396685987933937 1437168908547514490950453)
                ·
                  refine ⟨134734585176329483526605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1437168908547514490950453 134734585176329483526605)
                  ·
                    rfl

theorem cell21_590388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_590388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_590388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_590388 prefixEnd_590388 := by exact prefixLift 590388
  have htrace : WordTrace (prefixWord ++ tailWord_590388) baseStart_590388 baseEnd_590388 := by
    simpa [prefixWord, tailWord_590388, baseEnd_590388] using wordTrace_append hprefix tailTrace_590388
  have hstable : (prefixWord ++ tailWord_590388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590388).length < 2 ^ (prefixWord ++ tailWord_590388).sum := by decide
  have hdescent : baseEnd_590388 < baseStart_590388 := by decide
  rcases family_descends (prefixWord ++ tailWord_590388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590399 : List Nat := [1, 1, 2, 2, 3, 2, 5, 5]
def baseStart_590399 : Nat := 118140960795 + 590399 * 2 ^ 59
def prefixEnd_590399 : Nat := 4983230072969 + 3 ^ 40 * 590399 * 2
def baseEnd_590399 : Nat := 44912365175398636281083

theorem tailTrace_590399 : CollatzResearch.WordTrace tailWord_590399 prefixEnd_590399 44912365175398636281083 := by
  unfold tailWord_590399
  simp only [CollatzResearch.WordTrace]
  refine ⟨21533620588092729966654251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14355747058728486644436167 21533620588092729966654251)
  ·
    refine ⟨32300430882139094949981377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21533620588092729966654251 32300430882139094949981377)
    ·
      refine ⟨24225323161604321212486033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32300430882139094949981377 24225323161604321212486033)
      ·
        refine ⟨18168992371203240909364525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24225323161604321212486033 18168992371203240909364525)
        ·
          refine ⟨6813372139201215341011697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18168992371203240909364525 6813372139201215341011697)
          ·
            refine ⟨5110029104400911505758773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6813372139201215341011697 5110029104400911505758773)
            ·
              refine ⟨479065228537585453664885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5110029104400911505758773 479065228537585453664885)
              ·
                refine ⟨44912365175398636281083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 479065228537585453664885 44912365175398636281083)
                ·
                  rfl

theorem cell21_590399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 5].length) (baseStart_590399 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_590399 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_590399 prefixEnd_590399 := by exact prefixLift 590399
  have htrace : WordTrace (prefixWord ++ tailWord_590399) baseStart_590399 baseEnd_590399 := by
    simpa [prefixWord, tailWord_590399, baseEnd_590399] using wordTrace_append hprefix tailTrace_590399
  have hstable : (prefixWord ++ tailWord_590399).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590399).length < 2 ^ (prefixWord ++ tailWord_590399).sum := by decide
  have hdescent : baseEnd_590399 < baseStart_590399 := by decide
  rcases family_descends (prefixWord ++ tailWord_590399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590444 : List Nat := [2, 2, 1, 1, 3, 1, 2, 5, 4]
def baseStart_590444 : Nat := 118140960795 + 590444 * 2 ^ 59
def prefixEnd_590444 : Nat := 4983230072969 + 3 ^ 40 * 590444 * 2
def baseEnd_590444 : Nat := 134747365139285830593157

theorem tailTrace_590444 : CollatzResearch.WordTrace tailWord_590444 prefixEnd_590444 134747365139285830593157 := by
  unfold tailWord_590444
  simp only [CollatzResearch.WordTrace]
  refine ⟨10767630936464851326021193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14356841248619801768028257 10767630936464851326021193)
  ·
    refine ⟨8075723202348638494515895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10767630936464851326021193 8075723202348638494515895)
    ·
      refine ⟨12113584803522957741773843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8075723202348638494515895 12113584803522957741773843)
      ·
        refine ⟨18170377205284436612660765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12113584803522957741773843 18170377205284436612660765)
        ·
          refine ⟨6813891451981663729747787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18170377205284436612660765 6813891451981663729747787)
          ·
            refine ⟨10220837177972495594621681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6813891451981663729747787 10220837177972495594621681)
            ·
              refine ⟨7665627883479371695966261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10220837177972495594621681 7665627883479371695966261)
              ·
                refine ⟨718652614076191096496837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7665627883479371695966261 718652614076191096496837)
                ·
                  refine ⟨134747365139285830593157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 718652614076191096496837 134747365139285830593157)
                  ·
                    rfl

theorem cell21_590444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 4].length) (baseStart_590444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_590444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_590444 prefixEnd_590444 := by exact prefixLift 590444
  have htrace : WordTrace (prefixWord ++ tailWord_590444) baseStart_590444 baseEnd_590444 := by
    simpa [prefixWord, tailWord_590444, baseEnd_590444] using wordTrace_append hprefix tailTrace_590444
  have hstable : (prefixWord ++ tailWord_590444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590444).length < 2 ^ (prefixWord ++ tailWord_590444).sum := by decide
  have hdescent : baseEnd_590444 < baseStart_590444 := by decide
  rcases family_descends (prefixWord ++ tailWord_590444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590540 : List Nat := [2, 2, 1, 5, 1, 1, 4, 2, 3]
def baseStart_590540 : Nat := 118140960795 + 590540 * 2 ^ 59
def prefixEnd_590540 : Nat := 4983230072969 + 3 ^ 40 * 590540 * 2
def baseEnd_590540 : Nat := 134769273647210996992961

theorem tailTrace_590540 : CollatzResearch.WordTrace tailWord_590540 prefixEnd_590540 134769273647210996992961 := by
  unfold tailWord_590540
  simp only [CollatzResearch.WordTrace]
  refine ⟨10769381640290955523768537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14359175520387940698358049 10769381640290955523768537)
  ·
    refine ⟨8077036230218216642826403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10769381640290955523768537 8077036230218216642826403)
    ·
      refine ⟨12115554345327324964239605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8077036230218216642826403 12115554345327324964239605)
      ·
        refine ⟨1135833219874436715397463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12115554345327324964239605 1135833219874436715397463)
        ·
          refine ⟨1703749829811655073096195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1135833219874436715397463 1703749829811655073096195)
          ·
            refine ⟨2555624744717482609644293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1703749829811655073096195 2555624744717482609644293)
            ·
              refine ⟨479179639634527989308305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2555624744717482609644293 479179639634527989308305)
              ·
                refine ⟨359384729725895991981229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 479179639634527989308305 359384729725895991981229)
                ·
                  refine ⟨134769273647210996992961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 359384729725895991981229 134769273647210996992961)
                  ·
                    rfl

theorem cell21_590540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 2, 3].length) (baseStart_590540 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_590540 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_590540 prefixEnd_590540 := by exact prefixLift 590540
  have htrace : WordTrace (prefixWord ++ tailWord_590540) baseStart_590540 baseEnd_590540 := by
    simpa [prefixWord, tailWord_590540, baseEnd_590540] using wordTrace_append hprefix tailTrace_590540
  have hstable : (prefixWord ++ tailWord_590540).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590540).length < 2 ^ (prefixWord ++ tailWord_590540).sum := by decide
  have hdescent : baseEnd_590540 < baseStart_590540 := by decide
  rcases family_descends (prefixWord ++ tailWord_590540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590551 : List Nat := [1, 1, 3, 2, 1, 6, 1, 6]
def baseStart_590551 : Nat := 118140960795 + 590551 * 2 ^ 59
def prefixEnd_590551 : Nat := 4983230072969 + 3 ^ 40 * 590551 * 2
def baseEnd_590551 : Nat := 44923927999025807436535

theorem tailTrace_590551 : CollatzResearch.WordTrace tailWord_590551 prefixEnd_590551 44923927999025807436535 := by
  unfold tailWord_590551
  simp only [CollatzResearch.WordTrace]
  refine ⟨21539164483542059926187507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14359442989028039950791671 21539164483542059926187507)
  ·
    refine ⟨32308746725313089889281261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21539164483542059926187507 32308746725313089889281261)
    ·
      refine ⟨12115780021992408708480473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32308746725313089889281261 12115780021992408708480473)
      ·
        refine ⟨9086835016494306531360355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12115780021992408708480473 9086835016494306531360355)
        ·
          refine ⟨13630252524741459797040533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9086835016494306531360355 13630252524741459797040533)
          ·
            refine ⟨638918087097255927986275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 13630252524741459797040533 638918087097255927986275)
            ·
              refine ⟨958377130645883891979413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 638918087097255927986275 958377130645883891979413)
              ·
                refine ⟨44923927999025807436535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 958377130645883891979413 44923927999025807436535)
                ·
                  rfl

theorem cell21_590551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 6].length) (baseStart_590551 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_590551 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_590551 prefixEnd_590551 := by exact prefixLift 590551
  have htrace : WordTrace (prefixWord ++ tailWord_590551) baseStart_590551 baseEnd_590551 := by
    simpa [prefixWord, tailWord_590551, baseEnd_590551] using wordTrace_append hprefix tailTrace_590551
  have hstable : (prefixWord ++ tailWord_590551).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590551).length < 2 ^ (prefixWord ++ tailWord_590551).sum := by decide
  have hdescent : baseEnd_590551 < baseStart_590551 := by decide
  rcases family_descends (prefixWord ++ tailWord_590551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590565 : List Nat := [1, 3, 1, 4, 1, 2, 1, 1, 7]
def baseStart_590565 : Nat := 118140960795 + 590565 * 2 ^ 59
def prefixEnd_590565 : Nat := 4983230072969 + 3 ^ 40 * 590565 * 2
def baseEnd_590565 : Nat := 134774978987816509076243

theorem tailTrace_590565 : CollatzResearch.WordTrace tailWord_590565 prefixEnd_590565 134774978987816509076243 := by
  unfold tailWord_590565
  simp only [CollatzResearch.WordTrace]
  refine ⟨21539675105491340317197149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14359783403660893544798099 21539675105491340317197149)
  ·
    refine ⟨8077378164559252618948931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21539675105491340317197149 8077378164559252618948931)
    ·
      refine ⟨12116067246838878928423397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8077378164559252618948931 12116067246838878928423397)
      ·
        refine ⟨2271762608782289799079387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12116067246838878928423397 2271762608782289799079387)
        ·
          refine ⟨3407643913173434698619081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2271762608782289799079387 3407643913173434698619081)
          ·
            refine ⟨2555732934880076023964311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3407643913173434698619081 2555732934880076023964311)
            ·
              refine ⟨3833599402320114035946467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2555732934880076023964311 3833599402320114035946467)
              ·
                refine ⟨5750399103480171053919701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3833599402320114035946467 5750399103480171053919701)
                ·
                  refine ⟨134774978987816509076243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5750399103480171053919701 134774978987816509076243)
                  ·
                    rfl

theorem cell21_590565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 7].length) (baseStart_590565 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_590565 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_590565 prefixEnd_590565 := by exact prefixLift 590565
  have htrace : WordTrace (prefixWord ++ tailWord_590565) baseStart_590565 baseEnd_590565 := by
    simpa [prefixWord, tailWord_590565, baseEnd_590565] using wordTrace_append hprefix tailTrace_590565
  have hstable : (prefixWord ++ tailWord_590565).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590565).length < 2 ^ (prefixWord ++ tailWord_590565).sum := by decide
  have hdescent : baseEnd_590565 < baseStart_590565 := by decide
  rcases family_descends (prefixWord ++ tailWord_590565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590568 : List Nat := [2, 1, 4, 1, 4, 1, 3, 5]
def baseStart_590568 : Nat := 118140960795 + 590568 * 2 ^ 59
def prefixEnd_590568 : Nat := 4983230072969 + 3 ^ 40 * 590568 * 2
def baseEnd_590568 : Nat := 44925221209563056842079

theorem tailTrace_590568 : CollatzResearch.WordTrace tailWord_590568 prefixEnd_590568 44925221209563056842079 := by
  unfold tailWord_590568
  simp only [CollatzResearch.WordTrace]
  refine ⟨10769892262240235914778179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14359856349653647886370905 10769892262240235914778179)
  ·
    refine ⟨16154838393360353872167269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10769892262240235914778179 16154838393360353872167269)
    ·
      refine ⟨3029032198755066351031363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16154838393360353872167269 3029032198755066351031363)
      ·
        refine ⟨4543548298132599526547045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3029032198755066351031363 4543548298132599526547045)
        ·
          refine ⟨851915305899862411227571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4543548298132599526547045 851915305899862411227571)
          ·
            refine ⟨1277872958849793616841357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 851915305899862411227571 1277872958849793616841357)
            ·
              refine ⟨479202359568672606315509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1277872958849793616841357 479202359568672606315509)
              ·
                refine ⟨44925221209563056842079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 479202359568672606315509 44925221209563056842079)
                ·
                  rfl

theorem cell21_590568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 5].length) (baseStart_590568 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_590568 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_590568 prefixEnd_590568 := by exact prefixLift 590568
  have htrace : WordTrace (prefixWord ++ tailWord_590568) baseStart_590568 baseEnd_590568 := by
    simpa [prefixWord, tailWord_590568, baseEnd_590568] using wordTrace_append hprefix tailTrace_590568
  have hstable : (prefixWord ++ tailWord_590568).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590568).length < 2 ^ (prefixWord ++ tailWord_590568).sum := by decide
  have hdescent : baseEnd_590568 < baseStart_590568 := by decide
  rcases family_descends (prefixWord ++ tailWord_590568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590579 : List Nat := [1, 1, 1, 2, 2, 3, 1, 4, 6]
def baseStart_590579 : Nat := 118140960795 + 590579 * 2 ^ 59
def prefixEnd_590579 : Nat := 4983230072969 + 3 ^ 40 * 590579 * 2
def baseEnd_590579 : Nat := 134778173978555595842881

theorem tailTrace_590579 : CollatzResearch.WordTrace tailWord_590579 prefixEnd_590579 134778173978555595842881 := by
  unfold tailWord_590579
  simp only [CollatzResearch.WordTrace]
  refine ⟨21540185727440620708206791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14360123818293747138804527 21540185727440620708206791)
  ·
    refine ⟨32310278591160931062310187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21540185727440620708206791 32310278591160931062310187)
    ·
      refine ⟨48465417886741396593465281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32310278591160931062310187 48465417886741396593465281)
      ·
        refine ⟨36349063415056047445098961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48465417886741396593465281 36349063415056047445098961)
        ·
          refine ⟨27261797561292035583824221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36349063415056047445098961 27261797561292035583824221)
          ·
            refine ⟨10223174085484513343934083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27261797561292035583824221 10223174085484513343934083)
            ·
              refine ⟨15334761128226770015901125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10223174085484513343934083 15334761128226770015901125)
              ·
                refine ⟨2875267711542519377981461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15334761128226770015901125 2875267711542519377981461)
                ·
                  refine ⟨134778173978555595842881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2875267711542519377981461 134778173978555595842881)
                  ·
                    rfl

theorem cell21_590579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 6].length) (baseStart_590579 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_590579 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_590579 prefixEnd_590579 := by exact prefixLift 590579
  have htrace : WordTrace (prefixWord ++ tailWord_590579) baseStart_590579 baseEnd_590579 := by
    simpa [prefixWord, tailWord_590579, baseEnd_590579] using wordTrace_append hprefix tailTrace_590579
  have hstable : (prefixWord ++ tailWord_590579).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590579).length < 2 ^ (prefixWord ++ tailWord_590579).sum := by decide
  have hdescent : baseEnd_590579 < baseStart_590579 := by decide
  rcases family_descends (prefixWord ++ tailWord_590579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590596 : List Nat := [2, 3, 2, 2, 1, 1, 3, 1, 6]
def baseStart_590596 : Nat := 118140960795 + 590596 * 2 ^ 59
def prefixEnd_590596 : Nat := 4983230072969 + 3 ^ 40 * 590596 * 2
def baseEnd_590596 : Nat := 134782053610167344059513

theorem tailTrace_590596 : CollatzResearch.WordTrace tailWord_590596 prefixEnd_590596 134782053610167344059513 := by
  unfold tailWord_590596
  simp only [CollatzResearch.WordTrace]
  refine ⟨10770402884189516305787821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14360537178919355074383761 10770402884189516305787821)
  ·
    refine ⟨4038901081571068614670433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10770402884189516305787821 4038901081571068614670433)
    ·
      refine ⟨3029175811178301461002825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4038901081571068614670433 3029175811178301461002825)
      ·
        refine ⟨2271881858383726095752119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3029175811178301461002825 2271881858383726095752119)
        ·
          refine ⟨3407822787575589143628179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2271881858383726095752119 3407822787575589143628179)
          ·
            refine ⟨5111734181363383715442269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3407822787575589143628179 5111734181363383715442269)
            ·
              refine ⟨1916900318011268893290851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5111734181363383715442269 1916900318011268893290851)
              ·
                refine ⟨2875350477016903339936277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1916900318011268893290851 2875350477016903339936277)
                ·
                  refine ⟨134782053610167344059513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2875350477016903339936277 134782053610167344059513)
                  ·
                    rfl

theorem cell21_590596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_590596 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_590596 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_590596 prefixEnd_590596 := by exact prefixLift 590596
  have htrace : WordTrace (prefixWord ++ tailWord_590596) baseStart_590596 baseEnd_590596 := by
    simpa [prefixWord, tailWord_590596, baseEnd_590596] using wordTrace_append hprefix tailTrace_590596
  have hstable : (prefixWord ++ tailWord_590596).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590596).length < 2 ^ (prefixWord ++ tailWord_590596).sum := by decide
  have hdescent : baseEnd_590596 < baseStart_590596 := by decide
  rcases family_descends (prefixWord ++ tailWord_590596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590599 : List Nat := [1, 1, 4, 4, 1, 1, 2, 4, 3]
def baseStart_590599 : Nat := 118140960795 + 590599 * 2 ^ 59
def prefixEnd_590599 : Nat := 4983230072969 + 3 ^ 40 * 590599 * 2
def baseEnd_590599 : Nat := 134782738251040005509507

theorem tailTrace_590599 : CollatzResearch.WordTrace tailWord_590599 prefixEnd_590599 134782738251040005509507 := by
  unfold tailWord_590599
  simp only [CollatzResearch.WordTrace]
  refine ⟨21540915187368164123934851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14360610124912109415956567 21540915187368164123934851)
  ·
    refine ⟨32311372781052246185902277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21540915187368164123934851 32311372781052246185902277)
    ·
      refine ⟨6058382396447296159856677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32311372781052246185902277 6058382396447296159856677)
      ·
        refine ⟨1135946699333868029973127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6058382396447296159856677 1135946699333868029973127)
        ·
          refine ⟨1703920049000802044959691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1135946699333868029973127 1703920049000802044959691)
          ·
            refine ⟨2555880073501203067439537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1703920049000802044959691 2555880073501203067439537)
            ·
              refine ⟨1916910055125902300579653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2555880073501203067439537 1916910055125902300579653)
              ·
                refine ⟨359420635336106681358685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1916910055125902300579653 359420635336106681358685)
                ·
                  refine ⟨134782738251040005509507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 359420635336106681358685 134782738251040005509507)
                  ·
                    rfl

theorem cell21_590599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 4, 3].length) (baseStart_590599 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_590599 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_590599 prefixEnd_590599 := by exact prefixLift 590599
  have htrace : WordTrace (prefixWord ++ tailWord_590599) baseStart_590599 baseEnd_590599 := by
    simpa [prefixWord, tailWord_590599, baseEnd_590599] using wordTrace_append hprefix tailTrace_590599
  have hstable : (prefixWord ++ tailWord_590599).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590599).length < 2 ^ (prefixWord ++ tailWord_590599).sum := by decide
  have hdescent : baseEnd_590599 < baseStart_590599 := by decide
  rcases family_descends (prefixWord ++ tailWord_590599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590613 : List Nat := [1, 3, 2, 1, 2, 2, 5, 1, 4]
def baseStart_590613 : Nat := 118140960795 + 590613 * 2 ^ 59
def prefixEnd_590613 : Nat := 4983230072969 + 3 ^ 40 * 590613 * 2
def baseEnd_590613 : Nat := 134785933241779092276145

theorem tailTrace_590613 : CollatzResearch.WordTrace tailWord_590613 prefixEnd_590613 134785933241779092276145 := by
  unfold tailWord_590613
  simp only [CollatzResearch.WordTrace]
  refine ⟨21541425809317444514944493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14360950539544963009962995 21541425809317444514944493)
  ·
    refine ⟨8078034678494041693104185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21541425809317444514944493 8078034678494041693104185)
    ·
      refine ⟨6058526008870531269828139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8078034678494041693104185 6058526008870531269828139)
      ·
        refine ⟨9087789013305796904742209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6058526008870531269828139 9087789013305796904742209)
        ·
          refine ⟨6815841759979347678556657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9087789013305796904742209 6815841759979347678556657)
          ·
            refine ⟨5111881319984510758917493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6815841759979347678556657 5111881319984510758917493)
            ·
              refine ⟨479238873748547883648515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5111881319984510758917493 479238873748547883648515)
              ·
                refine ⟨718858310622821825472773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 479238873748547883648515 718858310622821825472773)
                ·
                  refine ⟨134785933241779092276145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 718858310622821825472773 134785933241779092276145)
                  ·
                    rfl

theorem cell21_590613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 1, 4].length) (baseStart_590613 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_590613 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_590613 prefixEnd_590613 := by exact prefixLift 590613
  have htrace : WordTrace (prefixWord ++ tailWord_590613) baseStart_590613 baseEnd_590613 := by
    simpa [prefixWord, tailWord_590613, baseEnd_590613] using wordTrace_append hprefix tailTrace_590613
  have hstable : (prefixWord ++ tailWord_590613).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590613).length < 2 ^ (prefixWord ++ tailWord_590613).sum := by decide
  have hdescent : baseEnd_590613 < baseStart_590613 := by decide
  rcases family_descends (prefixWord ++ tailWord_590613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590644 : List Nat := [2, 5, 1, 1, 3, 2, 7]
def baseStart_590644 : Nat := 118140960795 + 590644 * 2 ^ 59
def prefixEnd_590644 : Nat := 4983230072969 + 3 ^ 40 * 590644 * 2
def baseEnd_590644 : Nat := 14977000873792214139935

theorem tailTrace_590644 : CollatzResearch.WordTrace tailWord_590644 prefixEnd_590644 14977000873792214139935 := by
  unfold tailWord_590644
  simp only [CollatzResearch.WordTrace]
  refine ⟨10771278236102568404661493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14361704314803424539548657 10771278236102568404661493)
  ·
    refine ⟨1009807334634615787937015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10771278236102568404661493 1009807334634615787937015)
    ·
      refine ⟨1514711001951923681905523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1009807334634615787937015 1514711001951923681905523)
      ·
        refine ⟨2272066502927885522858285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1514711001951923681905523 2272066502927885522858285)
        ·
          refine ⟨852024938597957071071857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2272066502927885522858285 852024938597957071071857)
          ·
            refine ⟨639018703948467803303893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 852024938597957071071857 639018703948467803303893)
            ·
              refine ⟨14977000873792214139935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 639018703948467803303893 14977000873792214139935)
              ·
                rfl

theorem cell21_590644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 7].length) (baseStart_590644 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_590644 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_590644 prefixEnd_590644 := by exact prefixLift 590644
  have htrace : WordTrace (prefixWord ++ tailWord_590644) baseStart_590644 baseEnd_590644 := by
    simpa [prefixWord, tailWord_590644, baseEnd_590644] using wordTrace_append hprefix tailTrace_590644
  have hstable : (prefixWord ++ tailWord_590644).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590644).length < 2 ^ (prefixWord ++ tailWord_590644).sum := by decide
  have hdescent : baseEnd_590644 < baseStart_590644 := by decide
  rcases family_descends (prefixWord ++ tailWord_590644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590751 : List Nat := [1, 1, 2, 5, 2, 2, 2, 3, 3]
def baseStart_590751 : Nat := 118140960795 + 590751 * 2 ^ 59
def prefixEnd_590751 : Nat := 4983230072969 + 3 ^ 40 * 590751 * 2
def baseEnd_590751 : Nat := 134817426721921518975863

theorem tailTrace_590751 : CollatzResearch.WordTrace tailWord_590751 prefixEnd_590751 134817426721921518975863 := by
  unfold tailWord_590751
  simp only [CollatzResearch.WordTrace]
  refine ⟨21546459082817494083468107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14364306055211662722312071 21546459082817494083468107)
  ·
    refine ⟨32319688624226241125202161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21546459082817494083468107 32319688624226241125202161)
    ·
      refine ⟨24239766468169680843901621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32319688624226241125202161 24239766468169680843901621)
      ·
        refine ⟨2272478106390907579115777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24239766468169680843901621 2272478106390907579115777)
        ·
          refine ⟨1704358579793180684336833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2272478106390907579115777 1704358579793180684336833)
          ·
            refine ⟨1278268934844885513252625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1704358579793180684336833 1278268934844885513252625)
            ·
              refine ⟨958701701133664134939469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1278268934844885513252625 958701701133664134939469)
              ·
                refine ⟨359513137925124050602301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 958701701133664134939469 359513137925124050602301)
                ·
                  refine ⟨134817426721921518975863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 359513137925124050602301 134817426721921518975863)
                  ·
                    rfl

theorem cell21_590751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 3, 3].length) (baseStart_590751 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_590751 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_590751 prefixEnd_590751 := by exact prefixLift 590751
  have htrace : WordTrace (prefixWord ++ tailWord_590751) baseStart_590751 baseEnd_590751 := by
    simpa [prefixWord, tailWord_590751, baseEnd_590751] using wordTrace_append hprefix tailTrace_590751
  have hstable : (prefixWord ++ tailWord_590751).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590751).length < 2 ^ (prefixWord ++ tailWord_590751).sum := by decide
  have hdescent : baseEnd_590751 < baseStart_590751 := by decide
  rcases family_descends (prefixWord ++ tailWord_590751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590934 : List Nat := [5, 2, 2, 1, 2, 1, 1, 1, 6]
def baseStart_590934 : Nat := 118140960795 + 590934 * 2 ^ 59
def prefixEnd_590934 : Nat := 4983230072969 + 3 ^ 40 * 590934 * 2
def baseEnd_590934 : Nat := 134859189815153867425489

theorem tailTrace_590934 : CollatzResearch.WordTrace tailWord_590934 prefixEnd_590934 134859189815153867425489 := by
  unfold tailWord_590934
  simp only [CollatzResearch.WordTrace]
  refine ⟨1347070852572157271086241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14368755760769677558253237 1347070852572157271086241)
  ·
    refine ⟨1010303139429117953314681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1347070852572157271086241 1010303139429117953314681)
    ·
      refine ⟨757727354571838464986011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1010303139429117953314681 757727354571838464986011)
      ·
        refine ⟨1136591031857757697479017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 757727354571838464986011 1136591031857757697479017)
        ·
          refine ⟨852443273893318273109263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1136591031857757697479017 852443273893318273109263)
          ·
            refine ⟨1278664910839977409663895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 852443273893318273109263 1278664910839977409663895)
            ·
              refine ⟨1917997366259966114495843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1278664910839977409663895 1917997366259966114495843)
              ·
                refine ⟨2876996049389949171743765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1917997366259966114495843 2876996049389949171743765)
                ·
                  refine ⟨134859189815153867425489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2876996049389949171743765 134859189815153867425489)
                  ·
                    rfl

theorem cell21_590934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_590934 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_590934 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_590934 prefixEnd_590934 := by exact prefixLift 590934
  have htrace : WordTrace (prefixWord ++ tailWord_590934) baseStart_590934 baseEnd_590934 := by
    simpa [prefixWord, tailWord_590934, baseEnd_590934] using wordTrace_append hprefix tailTrace_590934
  have hstable : (prefixWord ++ tailWord_590934).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590934).length < 2 ^ (prefixWord ++ tailWord_590934).sum := by decide
  have hdescent : baseEnd_590934 < baseStart_590934 := by decide
  rcases family_descends (prefixWord ++ tailWord_590934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590965 : List Nat := [1, 3, 4, 3, 1, 2, 2, 5]
def baseStart_590965 : Nat := 118140960795 + 590965 * 2 ^ 59
def prefixEnd_590965 : Nat := 4983230072969 + 3 ^ 40 * 590965 * 2
def baseEnd_590965 : Nat := 44955421479168234136253

theorem tailTrace_590965 : CollatzResearch.WordTrace tailWord_590965 prefixEnd_590965 44955421479168234136253 := by
  unfold tailWord_590965
  simp only [CollatzResearch.WordTrace]
  refine ⟨21554264304042208631758349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14369509536028139087838899 21554264304042208631758349)
  ·
    refine ⟨8082849114015828236909381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21554264304042208631758349 8082849114015828236909381)
    ·
      refine ⟨1515534208877967794420509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8082849114015828236909381 1515534208877967794420509)
      ·
        refine ⟨568325328329237922907691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1515534208877967794420509 568325328329237922907691)
        ·
          refine ⟨852487992493856884361537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 568325328329237922907691 852487992493856884361537)
          ·
            refine ⟨639365994370392663271153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 852487992493856884361537 639365994370392663271153)
            ·
              refine ⟨479524495777794497453365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 639365994370392663271153 479524495777794497453365)
              ·
                refine ⟨44955421479168234136253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 479524495777794497453365 44955421479168234136253)
                ·
                  rfl

theorem cell21_590965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 5].length) (baseStart_590965 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_590965 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_590965 prefixEnd_590965 := by exact prefixLift 590965
  have htrace : WordTrace (prefixWord ++ tailWord_590965) baseStart_590965 baseEnd_590965 := by
    simpa [prefixWord, tailWord_590965, baseEnd_590965] using wordTrace_append hprefix tailTrace_590965
  have hstable : (prefixWord ++ tailWord_590965).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590965).length < 2 ^ (prefixWord ++ tailWord_590965).sum := by decide
  have hdescent : baseEnd_590965 < baseStart_590965 := by decide
  rcases family_descends (prefixWord ++ tailWord_590965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590990 : List Nat := [4, 1, 1, 3, 2, 1, 9]
def baseStart_590990 : Nat := 118140960795 + 590990 * 2 ^ 59
def prefixEnd_590990 : Nat := 4983230072969 + 3 ^ 40 * 590990 * 2
def baseEnd_590990 : Nat := 14985774419790023832449

theorem tailTrace_590990 : CollatzResearch.WordTrace tailWord_590990 prefixEnd_590990 14985774419790023832449 := by
  unfold tailWord_590990
  simp only [CollatzResearch.WordTrace]
  refine ⟨2694397016118954737677303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14370117419301091934278949 2694397016118954737677303)
  ·
    refine ⟨4041595524178432106515955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2694397016118954737677303 4041595524178432106515955)
    ·
      refine ⟨6062393286267648159773933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4041595524178432106515955 6062393286267648159773933)
      ·
        refine ⟨2273397482350368059915225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6062393286267648159773933 2273397482350368059915225)
        ·
          refine ⟨1705048111762776044936419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2273397482350368059915225 1705048111762776044936419)
          ·
            refine ⟨2557572167644164067404629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1705048111762776044936419 2557572167644164067404629)
            ·
              refine ⟨14985774419790023832449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2557572167644164067404629 14985774419790023832449)
              ·
                rfl

theorem cell21_590990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 9].length) (baseStart_590990 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_590990 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_590990 prefixEnd_590990 := by exact prefixLift 590990
  have htrace : WordTrace (prefixWord ++ tailWord_590990) baseStart_590990 baseEnd_590990 := by
    simpa [prefixWord, tailWord_590990, baseEnd_590990] using wordTrace_append hprefix tailTrace_590990
  have hstable : (prefixWord ++ tailWord_590990).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590990).length < 2 ^ (prefixWord ++ tailWord_590990).sum := by decide
  have hdescent : baseEnd_590990 < baseStart_590990 := by decide
  rcases family_descends (prefixWord ++ tailWord_590990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591007 : List Nat := [1, 1, 2, 6, 2, 1, 2, 6]
def baseStart_591007 : Nat := 118140960795 + 591007 * 2 ^ 59
def prefixEnd_591007 : Nat := 4983230072969 + 3 ^ 40 * 591007 * 2
def baseEnd_591007 : Nat := 44958616469907320902891

theorem tailTrace_591007 : CollatzResearch.WordTrace tailWord_591007 prefixEnd_591007 44958616469907320902891 := by
  unfold tailWord_591007
  simp only [CollatzResearch.WordTrace]
  refine ⟨21555796169890049804787275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14370530779926699869858183 21555796169890049804787275)
  ·
    refine ⟨32333694254835074707180913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21555796169890049804787275 32333694254835074707180913)
    ·
      refine ⟨24250270691126306030385685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32333694254835074707180913 24250270691126306030385685)
      ·
        refine ⟨1136731438646545595174329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 24250270691126306030385685 1136731438646545595174329)
        ·
          refine ⟨852548578984909196380747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1136731438646545595174329 852548578984909196380747)
          ·
            refine ⟨1278822868477363794571121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 852548578984909196380747 1278822868477363794571121)
            ·
              refine ⟨959117151358022845928341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1278822868477363794571121 959117151358022845928341)
              ·
                refine ⟨44958616469907320902891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 959117151358022845928341 44958616469907320902891)
                ·
                  rfl

theorem cell21_591007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 6].length) (baseStart_591007 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_591007 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_591007 prefixEnd_591007 := by exact prefixLift 591007
  have htrace : WordTrace (prefixWord ++ tailWord_591007) baseStart_591007 baseEnd_591007 := by
    simpa [prefixWord, tailWord_591007, baseEnd_591007] using wordTrace_append hprefix tailTrace_591007
  have hstable : (prefixWord ++ tailWord_591007).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591007).length < 2 ^ (prefixWord ++ tailWord_591007).sum := by decide
  have hdescent : baseEnd_591007 < baseStart_591007 := by decide
  rcases family_descends (prefixWord ++ tailWord_591007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591125 : List Nat := [1, 3, 2, 1, 2, 1, 1, 10]
def baseStart_591125 : Nat := 118140960795 + 591125 * 2 ^ 59
def prefixEnd_591125 : Nat := 4983230072969 + 3 ^ 40 * 591125 * 2
def baseEnd_591125 : Nat := 44967592872459993247255

theorem tailTrace_591125 : CollatzResearch.WordTrace tailWord_591125 prefixEnd_591125 44967592872459993247255 := by
  unfold tailWord_591125
  simp only [CollatzResearch.WordTrace]
  refine ⟨21560099983462555957582829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14373399988975037305055219 21560099983462555957582829)
  ·
    refine ⟨8085037493798458484093561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21560099983462555957582829 8085037493798458484093561)
    ·
      refine ⟨6063778120348843863070171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8085037493798458484093561 6063778120348843863070171)
      ·
        refine ⟨9095667180523265794605257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6063778120348843863070171 9095667180523265794605257)
        ·
          refine ⟨6821750385392449345953943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9095667180523265794605257 6821750385392449345953943)
          ·
            refine ⟨10232625578088674018930915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6821750385392449345953943 10232625578088674018930915)
            ·
              refine ⟨15348938367133011028396373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10232625578088674018930915 15348938367133011028396373)
              ·
                refine ⟨44967592872459993247255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 15348938367133011028396373 44967592872459993247255)
                ·
                  rfl

theorem cell21_591125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 10].length) (baseStart_591125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_591125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_591125 prefixEnd_591125 := by exact prefixLift 591125
  have htrace : WordTrace (prefixWord ++ tailWord_591125) baseStart_591125 baseEnd_591125 := by
    simpa [prefixWord, tailWord_591125, baseEnd_591125] using wordTrace_append hprefix tailTrace_591125
  have hstable : (prefixWord ++ tailWord_591125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591125).length < 2 ^ (prefixWord ++ tailWord_591125).sum := by decide
  have hdescent : baseEnd_591125 < baseStart_591125 := by decide
  rcases family_descends (prefixWord ++ tailWord_591125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591134 : List Nat := [4, 3, 2, 1, 3, 1, 2, 5]
def baseStart_591134 : Nat := 118140960795 + 591134 * 2 ^ 59
def prefixEnd_591134 : Nat := 4983230072969 + 3 ^ 40 * 591134 * 2
def baseEnd_591134 : Nat := 44968277513332654697249

theorem tailTrace_591134 : CollatzResearch.WordTrace tailWord_591134 prefixEnd_591134 44968277513332654697249 := by
  unfold tailWord_591134
  simp only [CollatzResearch.WordTrace]
  refine ⟨2695053530053743811832557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14373618826953300329773637 2695053530053743811832557)
  ·
    refine ⟨1010645073770153929437209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2695053530053743811832557 1010645073770153929437209)
    ·
      refine ⟨757983805327615447077907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1010645073770153929437209 757983805327615447077907)
      ·
        refine ⟨1136975707991423170616861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 757983805327615447077907 1136975707991423170616861)
        ·
          refine ⟨426365890496783688981323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1136975707991423170616861 426365890496783688981323)
          ·
            refine ⟨639548835745175533471985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 426365890496783688981323 639548835745175533471985)
            ·
              refine ⟨479661626808881650103989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 639548835745175533471985 479661626808881650103989)
              ·
                refine ⟨44968277513332654697249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 479661626808881650103989 44968277513332654697249)
                ·
                  rfl

theorem cell21_591134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 5].length) (baseStart_591134 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_591134 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_591134 prefixEnd_591134 := by exact prefixLift 591134
  have htrace : WordTrace (prefixWord ++ tailWord_591134) baseStart_591134 baseEnd_591134 := by
    simpa [prefixWord, tailWord_591134, baseEnd_591134] using wordTrace_append hprefix tailTrace_591134
  have hstable : (prefixWord ++ tailWord_591134).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591134).length < 2 ^ (prefixWord ++ tailWord_591134).sum := by decide
  have hdescent : baseEnd_591134 < baseStart_591134 := by decide
  rcases family_descends (prefixWord ++ tailWord_591134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591173 : List Nat := [1, 3, 1, 1, 1, 2, 1, 8, 3]
def baseStart_591173 : Nat := 118140960795 + 591173 * 2 ^ 59
def prefixEnd_591173 : Nat := 4983230072969 + 3 ^ 40 * 591173 * 2
def baseEnd_591173 : Nat := 134913732871342562941667

theorem tailTrace_591173 : CollatzResearch.WordTrace tailWord_591173 prefixEnd_591173 134913732871342562941667 := by
  unfold tailWord_591173
  simp only [CollatzResearch.WordTrace]
  refine ⟨21561850687288660155330173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14374567124859106770220115 21561850687288660155330173)
  ·
    refine ⟨8085694007733247558248815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21561850687288660155330173 8085694007733247558248815)
    ·
      refine ⟨12128541011599871337373223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8085694007733247558248815 12128541011599871337373223)
      ·
        refine ⟨18192811517399807006059835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12128541011599871337373223 18192811517399807006059835)
        ·
          refine ⟨27289217276099710509089753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18192811517399807006059835 27289217276099710509089753)
          ·
            refine ⟨20466912957074782881817315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27289217276099710509089753 20466912957074782881817315)
            ·
              refine ⟨30700369435612174322725973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20466912957074782881817315 30700369435612174322725973)
              ·
                refine ⟨359769954323580167844445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 30700369435612174322725973 359769954323580167844445)
                ·
                  refine ⟨134913732871342562941667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 359769954323580167844445 134913732871342562941667)
                  ·
                    rfl

theorem cell21_591173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 8, 3].length) (baseStart_591173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_591173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_591173 prefixEnd_591173 := by exact prefixLift 591173
  have htrace : WordTrace (prefixWord ++ tailWord_591173) baseStart_591173 baseEnd_591173 := by
    simpa [prefixWord, tailWord_591173, baseEnd_591173] using wordTrace_append hprefix tailTrace_591173
  have hstable : (prefixWord ++ tailWord_591173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591173).length < 2 ^ (prefixWord ++ tailWord_591173).sum := by decide
  have hdescent : baseEnd_591173 < baseStart_591173 := by decide
  rcases family_descends (prefixWord ++ tailWord_591173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591187 : List Nat := [1, 1, 1, 2, 1, 1, 7, 3, 4]
def baseStart_591187 : Nat := 118140960795 + 591187 * 2 ^ 59
def prefixEnd_591187 : Nat := 4983230072969 + 3 ^ 40 * 591187 * 2
def baseEnd_591187 : Nat := 134916927862081649708305

theorem tailTrace_591187 : CollatzResearch.WordTrace tailWord_591187 prefixEnd_591187 134916927862081649708305 := by
  unfold tailWord_591187
  simp only [CollatzResearch.WordTrace]
  refine ⟨21562361309237940546339815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14374907539491960364226543 21562361309237940546339815)
  ·
    refine ⟨32343541963856910819509723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21562361309237940546339815 32343541963856910819509723)
    ·
      refine ⟨48515312945785366229264585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32343541963856910819509723 48515312945785366229264585)
      ·
        refine ⟨36386484709339024671948439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48515312945785366229264585 36386484709339024671948439)
        ·
          refine ⟨54579727064008537007922659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36386484709339024671948439 54579727064008537007922659)
          ·
            refine ⟨81869590596012805511883989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54579727064008537007922659 81869590596012805511883989)
            ·
              refine ⟨1918818529594050129184781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 81869590596012805511883989 1918818529594050129184781)
              ·
                refine ⟨719556948597768798444293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1918818529594050129184781 719556948597768798444293)
                ·
                  refine ⟨134916927862081649708305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 719556948597768798444293 134916927862081649708305)
                  ·
                    rfl

theorem cell21_591187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 3, 4].length) (baseStart_591187 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_591187 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_591187 prefixEnd_591187 := by exact prefixLift 591187
  have htrace : WordTrace (prefixWord ++ tailWord_591187) baseStart_591187 baseEnd_591187 := by
    simpa [prefixWord, tailWord_591187, baseEnd_591187] using wordTrace_append hprefix tailTrace_591187
  have hstable : (prefixWord ++ tailWord_591187).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591187).length < 2 ^ (prefixWord ++ tailWord_591187).sum := by decide
  have hdescent : baseEnd_591187 < baseStart_591187 := by decide
  rcases family_descends (prefixWord ++ tailWord_591187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591221 : List Nat := [1, 3, 4, 1, 3, 1, 2, 2, 4]
def baseStart_591221 : Nat := 118140960795 + 591221 * 2 ^ 59
def prefixEnd_591221 : Nat := 4983230072969 + 3 ^ 40 * 591221 * 2
def baseEnd_591221 : Nat := 134924687125305146141569

theorem tailTrace_591221 : CollatzResearch.WordTrace tailWord_591221 prefixEnd_591221 134924687125305146141569 := by
  unfold tailWord_591221
  simp only [CollatzResearch.WordTrace]
  refine ⟨21563601391114764353077517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14375734260743176235385011 21563601391114764353077517)
  ·
    refine ⟨8086350521668036632404069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21563601391114764353077517 8086350521668036632404069)
    ·
      refine ⟨1516190722812756868575763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8086350521668036632404069 1516190722812756868575763)
      ·
        refine ⟨2274286084219135302863645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1516190722812756868575763 2274286084219135302863645)
        ·
          refine ⟨852857281582175738573867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2274286084219135302863645 852857281582175738573867)
          ·
            refine ⟨1279285922373263607860801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 852857281582175738573867 1279285922373263607860801)
            ·
              refine ⟨959464441779947705895601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1279285922373263607860801 959464441779947705895601)
              ·
                refine ⟨719598331334960779421701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 959464441779947705895601 719598331334960779421701)
                ·
                  refine ⟨134924687125305146141569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 719598331334960779421701 134924687125305146141569)
                  ·
                    rfl

theorem cell21_591221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 2, 4].length) (baseStart_591221 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_591221 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_591221 prefixEnd_591221 := by exact prefixLift 591221
  have htrace : WordTrace (prefixWord ++ tailWord_591221) baseStart_591221 baseEnd_591221 := by
    simpa [prefixWord, tailWord_591221, baseEnd_591221] using wordTrace_append hprefix tailTrace_591221
  have hstable : (prefixWord ++ tailWord_591221).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591221).length < 2 ^ (prefixWord ++ tailWord_591221).sum := by decide
  have hdescent : baseEnd_591221 < baseStart_591221 := by decide
  rcases family_descends (prefixWord ++ tailWord_591221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591266 : List Nat := [3, 3, 1, 2, 1, 2, 1, 5, 3]
def baseStart_591266 : Nat := 118140960795 + 591266 * 2 ^ 59
def prefixEnd_591266 : Nat := 4983230072969 + 3 ^ 40 * 591266 * 2
def baseEnd_591266 : Nat := 134934956738395067891477

theorem tailTrace_591266 : CollatzResearch.WordTrace tailWord_591266 prefixEnd_591266 134934956738395067891477 := by
  unfold tailWord_591266
  simp only [CollatzResearch.WordTrace]
  refine ⟨5391310668987934259616413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14376828450634491358977101 5391310668987934259616413)
  ·
    refine ⟨2021741500870475347356155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5391310668987934259616413 2021741500870475347356155)
    ·
      refine ⟨3032612251305713021034233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2021741500870475347356155 3032612251305713021034233)
      ·
        refine ⟨2274459188479284765775675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3032612251305713021034233 2274459188479284765775675)
        ·
          refine ⟨3411688782718927148663513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2274459188479284765775675 3411688782718927148663513)
          ·
            refine ⟨2558766587039195361497635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3411688782718927148663513 2558766587039195361497635)
            ·
              refine ⟨3838149880558793042246453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2558766587039195361497635 3838149880558793042246453)
              ·
                refine ⟨359826551302386847710605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3838149880558793042246453 359826551302386847710605)
                ·
                  refine ⟨134934956738395067891477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 359826551302386847710605 134934956738395067891477)
                  ·
                    rfl

theorem cell21_591266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_591266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_591266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_591266 prefixEnd_591266 := by exact prefixLift 591266
  have htrace : WordTrace (prefixWord ++ tailWord_591266) baseStart_591266 baseEnd_591266 := by
    simpa [prefixWord, tailWord_591266, baseEnd_591266] using wordTrace_append hprefix tailTrace_591266
  have hstable : (prefixWord ++ tailWord_591266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591266).length < 2 ^ (prefixWord ++ tailWord_591266).sum := by decide
  have hdescent : baseEnd_591266 < baseStart_591266 := by decide
  rcases family_descends (prefixWord ++ tailWord_591266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591356 : List Nat := [2, 2, 2, 1, 2, 1, 6, 1, 4]
def baseStart_591356 : Nat := 118140960795 + 591356 * 2 ^ 59
def prefixEnd_591356 : Nat := 4983230072969 + 3 ^ 40 * 591356 * 2
def baseEnd_591356 : Nat := 134955495964574911391293

theorem tailTrace_591356 : CollatzResearch.WordTrace tailWord_591356 prefixEnd_591356 134955495964574911391293 := by
  unfold tailWord_591356
  simp only [CollatzResearch.WordTrace]
  refine ⟨10784262622812841204620961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14379016830417121606161281 10784262622812841204620961)
  ·
    refine ⟨8088196967109630903465721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10784262622812841204620961 8088196967109630903465721)
    ·
      refine ⟨6066147725332223177599291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8088196967109630903465721 6066147725332223177599291)
      ·
        refine ⟨9099221587998334766398937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6066147725332223177599291 9099221587998334766398937)
        ·
          refine ⟨6824416190998751074799203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9099221587998334766398937 6824416190998751074799203)
          ·
            refine ⟨10236624286498126612198805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6824416190998751074799203 10236624286498126612198805)
            ·
              refine ⟨479841763429599684946819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10236624286498126612198805 479841763429599684946819)
              ·
                refine ⟨719762645144399527420229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 479841763429599684946819 719762645144399527420229)
                ·
                  refine ⟨134955495964574911391293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 719762645144399527420229 134955495964574911391293)
                  ·
                    rfl

theorem cell21_591356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 1, 4].length) (baseStart_591356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_591356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_591356 prefixEnd_591356 := by exact prefixLift 591356
  have htrace : WordTrace (prefixWord ++ tailWord_591356) baseStart_591356 baseEnd_591356 := by
    simpa [prefixWord, tailWord_591356, baseEnd_591356] using wordTrace_append hprefix tailTrace_591356
  have hstable : (prefixWord ++ tailWord_591356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591356).length < 2 ^ (prefixWord ++ tailWord_591356).sum := by decide
  have hdescent : baseEnd_591356 < baseStart_591356 := by decide
  rcases family_descends (prefixWord ++ tailWord_591356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591415 : List Nat := [1, 1, 3, 1, 2, 4, 2, 3, 4]
def baseStart_591415 : Nat := 118140960795 + 591415 * 2 ^ 59
def prefixEnd_591415 : Nat := 4983230072969 + 3 ^ 40 * 591415 * 2
def baseEnd_591415 : Nat := 134968960568403919907839

theorem tailTrace_591415 : CollatzResearch.WordTrace tailWord_591415 prefixEnd_591415 134968960568403919907839 := by
  unfold tailWord_591415
  simp only [CollatzResearch.WordTrace]
  refine ⟨21570677152411935485639699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14380451434941290323759799 21570677152411935485639699)
  ·
    refine ⟨32356015728617903228459549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21570677152411935485639699 32356015728617903228459549)
    ·
      refine ⟨12133505898231713710672331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32356015728617903228459549 12133505898231713710672331)
      ·
        refine ⟨18200258847347570566008497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12133505898231713710672331 18200258847347570566008497)
        ·
          refine ⟨13650194135510677924506373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18200258847347570566008497 13650194135510677924506373)
          ·
            refine ⟨2559411400408252110844945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13650194135510677924506373 2559411400408252110844945)
            ·
              refine ⟨1919558550306189083133709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2559411400408252110844945 1919558550306189083133709)
              ·
                refine ⟨719834456364820906175141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1919558550306189083133709 719834456364820906175141)
                ·
                  refine ⟨134968960568403919907839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 719834456364820906175141 134968960568403919907839)
                  ·
                    rfl

theorem cell21_591415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 3, 4].length) (baseStart_591415 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_591415 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_591415 prefixEnd_591415 := by exact prefixLift 591415
  have htrace : WordTrace (prefixWord ++ tailWord_591415) baseStart_591415 baseEnd_591415 := by
    simpa [prefixWord, tailWord_591415, baseEnd_591415] using wordTrace_append hprefix tailTrace_591415
  have hstable : (prefixWord ++ tailWord_591415).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591415).length < 2 ^ (prefixWord ++ tailWord_591415).sum := by decide
  have hdescent : baseEnd_591415 < baseStart_591415 := by decide
  rcases family_descends (prefixWord ++ tailWord_591415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591460 : List Nat := [2, 3, 1, 1, 2, 3, 1, 3, 5]
def baseStart_591460 : Nat := 118140960795 + 591460 * 2 ^ 59
def prefixEnd_591460 : Nat := 4983230072969 + 3 ^ 40 * 591460 * 2
def baseEnd_591460 : Nat := 134979230181493841657747

theorem tailTrace_591460 : CollatzResearch.WordTrace tailWord_591460 prefixEnd_591460 134979230181493841657747 := by
  unfold tailWord_591460
  simp only [CollatzResearch.WordTrace]
  refine ⟨10786159218624454085513917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14381545624832605447351889 10786159218624454085513917)
  ·
    refine ⟨4044809706984170282067719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10786159218624454085513917 4044809706984170282067719)
    ·
      refine ⟨6067214560476255423101579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4044809706984170282067719 6067214560476255423101579)
      ·
        refine ⟨9100821840714383134652369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6067214560476255423101579 9100821840714383134652369)
        ·
          refine ⟨6825616380535787350989277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9100821840714383134652369 6825616380535787350989277)
          ·
            refine ⟨2559606142700920256620979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6825616380535787350989277 2559606142700920256620979)
            ·
              refine ⟨3839409214051380384931469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2559606142700920256620979 3839409214051380384931469)
              ·
                refine ⟨1439778455269267644349301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3839409214051380384931469 1439778455269267644349301)
                ·
                  refine ⟨134979230181493841657747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1439778455269267644349301 134979230181493841657747)
                  ·
                    rfl

theorem cell21_591460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_591460 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_591460 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_591460 prefixEnd_591460 := by exact prefixLift 591460
  have htrace : WordTrace (prefixWord ++ tailWord_591460) baseStart_591460 baseEnd_591460 := by
    simpa [prefixWord, tailWord_591460, baseEnd_591460] using wordTrace_append hprefix tailTrace_591460
  have hstable : (prefixWord ++ tailWord_591460).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591460).length < 2 ^ (prefixWord ++ tailWord_591460).sum := by decide
  have hdescent : baseEnd_591460 < baseStart_591460 := by decide
  rcases family_descends (prefixWord ++ tailWord_591460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591477 : List Nat := [1, 3, 4, 2, 1, 1, 2, 2, 5]
def baseStart_591477 : Nat := 118140960795 + 591477 * 2 ^ 59
def prefixEnd_591477 : Nat := 4983230072969 + 3 ^ 40 * 591477 * 2
def baseEnd_591477 : Nat := 134983109813105589874379

theorem tailTrace_591477 : CollatzResearch.WordTrace tailWord_591477 prefixEnd_591477 134983109813105589874379 := by
  unfold tailWord_591477
  simp only [CollatzResearch.WordTrace]
  refine ⟨21572938478187320074396685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14381958985458213382931123 21572938478187320074396685)
  ·
    refine ⟨8089851929320245027898757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21572938478187320074396685 8089851929320245027898757)
    ·
      refine ⟨1516847236747545942731017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8089851929320245027898757 1516847236747545942731017)
      ·
        refine ⟨1137635427560659457048263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1516847236747545942731017 1137635427560659457048263)
        ·
          refine ⟨1706453141340989185572395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1137635427560659457048263 1706453141340989185572395)
          ·
            refine ⟨2559679712011483778358593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1706453141340989185572395 2559679712011483778358593)
            ·
              refine ⟨1919759784008612833768945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2559679712011483778358593 1919759784008612833768945)
              ·
                refine ⟨1439819838006459625326709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1919759784008612833768945 1439819838006459625326709)
                ·
                  refine ⟨134983109813105589874379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1439819838006459625326709 134983109813105589874379)
                  ·
                    rfl

theorem cell21_591477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 2, 5].length) (baseStart_591477 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_591477 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_591477 prefixEnd_591477 := by exact prefixLift 591477
  have htrace : WordTrace (prefixWord ++ tailWord_591477) baseStart_591477 baseEnd_591477 := by
    simpa [prefixWord, tailWord_591477, baseEnd_591477] using wordTrace_append hprefix tailTrace_591477
  have hstable : (prefixWord ++ tailWord_591477).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591477).length < 2 ^ (prefixWord ++ tailWord_591477).sum := by decide
  have hdescent : baseEnd_591477 < baseStart_591477 := by decide
  rcases family_descends (prefixWord ++ tailWord_591477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591570 : List Nat := [3, 2, 2, 2, 2, 2, 1, 4, 3]
def baseStart_591570 : Nat := 118140960795 + 591570 * 2 ^ 59
def prefixEnd_591570 : Nat := 4983230072969 + 3 ^ 40 * 591570 * 2
def baseEnd_591570 : Nat := 135004333680158094824189

theorem tailTrace_591570 : CollatzResearch.WordTrace tailWord_591570 prefixEnd_591570 135004333680158094824189 := by
  unfold tailWord_591570
  simp only [CollatzResearch.WordTrace]
  refine ⟨5394082616712599239383041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14384220311233597971688109 5394082616712599239383041)
  ·
    refine ⟨4045561962534449429537281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5394082616712599239383041 4045561962534449429537281)
    ·
      refine ⟨3034171471900837072152961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4045561962534449429537281 3034171471900837072152961)
      ·
        refine ⟨2275628603925627804114721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3034171471900837072152961 2275628603925627804114721)
        ·
          refine ⟨1706721452944220853086041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2275628603925627804114721 1706721452944220853086041)
          ·
            refine ⟨1280041089708165639814531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1706721452944220853086041 1280041089708165639814531)
            ·
              refine ⟨1920061634562248459721797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1280041089708165639814531 1920061634562248459721797)
              ·
                refine ⟨360011556480421586197837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1920061634562248459721797 360011556480421586197837)
                ·
                  refine ⟨135004333680158094824189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 360011556480421586197837 135004333680158094824189)
                  ·
                    rfl

theorem cell21_591570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 4, 3].length) (baseStart_591570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_591570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_591570 prefixEnd_591570 := by exact prefixLift 591570
  have htrace : WordTrace (prefixWord ++ tailWord_591570) baseStart_591570 baseEnd_591570 := by
    simpa [prefixWord, tailWord_591570, baseEnd_591570] using wordTrace_append hprefix tailTrace_591570
  have hstable : (prefixWord ++ tailWord_591570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591570).length < 2 ^ (prefixWord ++ tailWord_591570).sum := by decide
  have hdescent : baseEnd_591570 < baseStart_591570 := by decide
  rcases family_descends (prefixWord ++ tailWord_591570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591595 : List Nat := [1, 1, 1, 1, 2, 4, 3, 1, 7]
def baseStart_591595 : Nat := 118140960795 + 591595 * 2 ^ 59
def prefixEnd_591595 : Nat := 4983230072969 + 3 ^ 40 * 591595 * 2
def baseEnd_591595 : Nat := 135010039020763606907471

theorem tailTrace_591595 : CollatzResearch.WordTrace tailWord_591595 prefixEnd_591595 135010039020763606907471 := by
  unfold tailWord_591595
  simp only [CollatzResearch.WordTrace]
  refine ⟨21577242291759826227192239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14384828194506550818128159 21577242291759826227192239)
  ·
    refine ⟨32365863437639739340788359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21577242291759826227192239 32365863437639739340788359)
    ·
      refine ⟨48548795156459609011182539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32365863437639739340788359 48548795156459609011182539)
      ·
        refine ⟨72823192734689413516773809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48548795156459609011182539 72823192734689413516773809)
        ·
          refine ⟨54617394551017060137580357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72823192734689413516773809 54617394551017060137580357)
          ·
            refine ⟨10240761478315698775796317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54617394551017060137580357 10240761478315698775796317)
            ·
              refine ⟨3840285554368387040923619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10240761478315698775796317 3840285554368387040923619)
              ·
                refine ⟨5760428331552580561385429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3840285554368387040923619 5760428331552580561385429)
                ·
                  refine ⟨135010039020763606907471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5760428331552580561385429 135010039020763606907471)
                  ·
                    rfl

theorem cell21_591595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 7].length) (baseStart_591595 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_591595 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_591595 prefixEnd_591595 := by exact prefixLift 591595
  have htrace : WordTrace (prefixWord ++ tailWord_591595) baseStart_591595 baseEnd_591595 := by
    simpa [prefixWord, tailWord_591595, baseEnd_591595] using wordTrace_append hprefix tailTrace_591595
  have hstable : (prefixWord ++ tailWord_591595).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591595).length < 2 ^ (prefixWord ++ tailWord_591595).sum := by decide
  have hdescent : baseEnd_591595 < baseStart_591595 := by decide
  rcases family_descends (prefixWord ++ tailWord_591595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591598 : List Nat := [4, 1, 2, 1, 1, 2, 5, 5]
def baseStart_591598 : Nat := 118140960795 + 591598 * 2 ^ 59
def prefixEnd_591598 : Nat := 4983230072969 + 3 ^ 40 * 591598 * 2
def baseEnd_591598 : Nat := 45003574553878756119155

theorem tailTrace_591598 : CollatzResearch.WordTrace tailWord_591598 prefixEnd_591598 45003574553878756119155 := by
  unfold tailWord_591598
  simp only [CollatzResearch.WordTrace]
  refine ⟨2697168963843619717443931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14384901140499305159700965 2697168963843619717443931)
  ·
    refine ⟨4045753445765429576165897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2697168963843619717443931 4045753445765429576165897)
    ·
      refine ⟨3034315084324072182124423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4045753445765429576165897 3034315084324072182124423)
      ·
        refine ⟨4551472626486108273186635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3034315084324072182124423 4551472626486108273186635)
        ·
          refine ⟨6827208939729162409779953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4551472626486108273186635 6827208939729162409779953)
          ·
            refine ⟨5120406704796871807334965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6827208939729162409779953 5120406704796871807334965)
            ·
              refine ⟨480038128574706731937653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5120406704796871807334965 480038128574706731937653)
              ·
                refine ⟨45003574553878756119155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 480038128574706731937653 45003574553878756119155)
                ·
                  rfl

theorem cell21_591598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 5].length) (baseStart_591598 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_591598 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_591598 prefixEnd_591598 := by exact prefixLift 591598
  have htrace : WordTrace (prefixWord ++ tailWord_591598) baseStart_591598 baseEnd_591598 := by
    simpa [prefixWord, tailWord_591598, baseEnd_591598] using wordTrace_append hprefix tailTrace_591598
  have hstable : (prefixWord ++ tailWord_591598).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591598).length < 2 ^ (prefixWord ++ tailWord_591598).sum := by decide
  have hdescent : baseEnd_591598 < baseStart_591598 := by decide
  rcases family_descends (prefixWord ++ tailWord_591598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591604 : List Nat := [2, 6, 1, 1, 1, 2, 2, 3, 3]
def baseStart_591604 : Nat := 118140960795 + 591604 * 2 ^ 59
def prefixEnd_591604 : Nat := 4983230072969 + 3 ^ 40 * 591604 * 2
def baseEnd_591604 : Nat := 135012092943381591257453

theorem tailTrace_591604 : CollatzResearch.WordTrace tailWord_591604 prefixEnd_591604 135012092943381591257453 := by
  unfold tailWord_591604
  simp only [CollatzResearch.WordTrace]
  refine ⟨10788785274363610382134933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14385047032484813842846577 10788785274363610382134933)
  ·
    refine ⟨505724309735794236662575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10788785274363610382134933 505724309735794236662575)
    ·
      refine ⟨758586464603691354993863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 505724309735794236662575 758586464603691354993863)
      ·
        refine ⟨1137879696905537032490795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 758586464603691354993863 1137879696905537032490795)
        ·
          refine ⟨1706819545358305548736193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1137879696905537032490795 1706819545358305548736193)
          ·
            refine ⟨1280114659018729161552145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1706819545358305548736193 1280114659018729161552145)
            ·
              refine ⟨960085994264046871164109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1280114659018729161552145 960085994264046871164109)
              ·
                refine ⟨360032247849017576686541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 960085994264046871164109 360032247849017576686541)
                ·
                  refine ⟨135012092943381591257453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 360032247849017576686541 135012092943381591257453)
                  ·
                    rfl

theorem cell21_591604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_591604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_591604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_591604 prefixEnd_591604 := by exact prefixLift 591604
  have htrace : WordTrace (prefixWord ++ tailWord_591604) baseStart_591604 baseEnd_591604 := by
    simpa [prefixWord, tailWord_591604, baseEnd_591604] using wordTrace_append hprefix tailTrace_591604
  have hstable : (prefixWord ++ tailWord_591604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591604).length < 2 ^ (prefixWord ++ tailWord_591604).sum := by decide
  have hdescent : baseEnd_591604 < baseStart_591604 := by decide
  rcases family_descends (prefixWord ++ tailWord_591604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591688 : List Nat := [2, 1, 3, 1, 1, 4, 3, 1, 5]
def baseStart_591688 : Nat := 118140960795 + 591688 * 2 ^ 59
def prefixEnd_591688 : Nat := 4983230072969 + 3 ^ 40 * 591688 * 2
def baseEnd_591688 : Nat := 135031262887816111857281

theorem tailTrace_591688 : CollatzResearch.WordTrace tailWord_591688 prefixEnd_591688 135031262887816111857281 := by
  unfold tailWord_591688
  simp only [CollatzResearch.WordTrace]
  refine ⟨10790317140211451555163859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14387089520281935406885145 10790317140211451555163859)
  ·
    refine ⟨16185475710317177332745789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10790317140211451555163859 16185475710317177332745789)
    ·
      refine ⟨6069553391368941499779671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16185475710317177332745789 6069553391368941499779671)
      ·
        refine ⟨9104330087053412249669507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6069553391368941499779671 9104330087053412249669507)
        ·
          refine ⟨13656495130580118374504261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9104330087053412249669507 13656495130580118374504261)
          ·
            refine ⟨2560592836983772195219549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13656495130580118374504261 2560592836983772195219549)
            ·
              refine ⟨960222313868914573207331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2560592836983772195219549 960222313868914573207331)
              ·
                refine ⟨1440333470803371859810997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 960222313868914573207331 1440333470803371859810997)
                ·
                  refine ⟨135031262887816111857281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1440333470803371859810997 135031262887816111857281)
                  ·
                    rfl

theorem cell21_591688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 1, 5].length) (baseStart_591688 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_591688 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_591688 prefixEnd_591688 := by exact prefixLift 591688
  have htrace : WordTrace (prefixWord ++ tailWord_591688) baseStart_591688 baseEnd_591688 := by
    simpa [prefixWord, tailWord_591688, baseEnd_591688] using wordTrace_append hprefix tailTrace_591688
  have hstable : (prefixWord ++ tailWord_591688).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591688).length < 2 ^ (prefixWord ++ tailWord_591688).sum := by decide
  have hdescent : baseEnd_591688 < baseStart_591688 := by decide
  rcases family_descends (prefixWord ++ tailWord_591688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591764 : List Nat := [2, 4, 2, 1, 1, 2, 1, 1, 7]
def baseStart_591764 : Nat := 118140960795 + 591764 * 2 ^ 59
def prefixEnd_591764 : Nat := 4983230072969 + 3 ^ 40 * 591764 * 2
def baseEnd_591764 : Nat := 135048607123256868590459

theorem tailTrace_591764 : CollatzResearch.WordTrace tailWord_591764 prefixEnd_591764 135048607123256868590459 := by
  unfold tailWord_591764
  simp only [CollatzResearch.WordTrace]
  refine ⟨10791703114073784045047173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14388937485431712060062897 10791703114073784045047173)
  ·
    refine ⟨2023444333888834508446345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10791703114073784045047173 2023444333888834508446345)
    ·
      refine ⟨1517583250416625881334759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2023444333888834508446345 1517583250416625881334759)
      ·
        refine ⟨2276374875624938822002139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1517583250416625881334759 2276374875624938822002139)
        ·
          refine ⟨3414562313437408233003209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2276374875624938822002139 3414562313437408233003209)
          ·
            refine ⟨2560921735078056174752407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3414562313437408233003209 2560921735078056174752407)
            ·
              refine ⟨3841382602617084262128611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2560921735078056174752407 3841382602617084262128611)
              ·
                refine ⟨5762073903925626393192917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3841382602617084262128611 5762073903925626393192917)
                ·
                  refine ⟨135048607123256868590459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5762073903925626393192917 135048607123256868590459)
                  ·
                    rfl

theorem cell21_591764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_591764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_591764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_591764 prefixEnd_591764 := by exact prefixLift 591764
  have htrace : WordTrace (prefixWord ++ tailWord_591764) baseStart_591764 baseEnd_591764 := by
    simpa [prefixWord, tailWord_591764, baseEnd_591764] using wordTrace_append hprefix tailTrace_591764
  have hstable : (prefixWord ++ tailWord_591764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591764).length < 2 ^ (prefixWord ++ tailWord_591764).sum := by decide
  have hdescent : baseEnd_591764 < baseStart_591764 := by decide
  rcases family_descends (prefixWord ++ tailWord_591764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591823 : List Nat := [1, 1, 2, 1, 1, 5, 1, 4, 5]
def baseStart_591823 : Nat := 118140960795 + 591823 * 2 ^ 59
def prefixEnd_591823 : Nat := 4983230072969 + 3 ^ 40 * 591823 * 2
def baseEnd_591823 : Nat := 135062071727085877107005

theorem tailTrace_591823 : CollatzResearch.WordTrace tailWord_591823 prefixEnd_591823 135062071727085877107005 := by
  unfold tailWord_591823
  simp only [CollatzResearch.WordTrace]
  refine ⟨21585558134933821166492123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14390372089955880777661415 21585558134933821166492123)
  ·
    refine ⟨32378337202400731749738185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21585558134933821166492123 32378337202400731749738185)
    ·
      refine ⟨24283752901800548812303639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32378337202400731749738185 24283752901800548812303639)
      ·
        refine ⟨36425629352700823218455459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24283752901800548812303639 36425629352700823218455459)
        ·
          refine ⟨54638444029051234827683189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36425629352700823218455459 54638444029051234827683189)
          ·
            refine ⟨5122354127723553265095299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54638444029051234827683189 5122354127723553265095299)
            ·
              refine ⟨7683531191585329897642949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5122354127723553265095299 7683531191585329897642949)
              ·
                refine ⟨1440662098422249355808053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7683531191585329897642949 1440662098422249355808053)
                ·
                  refine ⟨135062071727085877107005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1440662098422249355808053 135062071727085877107005)
                  ·
                    rfl

theorem cell21_591823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4, 5].length) (baseStart_591823 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_591823 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_591823 prefixEnd_591823 := by exact prefixLift 591823
  have htrace : WordTrace (prefixWord ++ tailWord_591823) baseStart_591823 baseEnd_591823 := by
    simpa [prefixWord, tailWord_591823, baseEnd_591823] using wordTrace_append hprefix tailTrace_591823
  have hstable : (prefixWord ++ tailWord_591823).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591823).length < 2 ^ (prefixWord ++ tailWord_591823).sum := by decide
  have hdescent : baseEnd_591823 < baseStart_591823 := by decide
  rcases family_descends (prefixWord ++ tailWord_591823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591826 : List Nat := [3, 2, 2, 3, 2, 1, 1, 7]
def baseStart_591826 : Nat := 118140960795 + 591826 * 2 ^ 59
def prefixEnd_591826 : Nat := 4983230072969 + 3 ^ 40 * 591826 * 2
def baseEnd_591826 : Nat := 45020918789319512852333

theorem tailTrace_591826 : CollatzResearch.WordTrace tailWord_591826 prefixEnd_591826 45020918789319512852333 := by
  unfold tailWord_591826
  simp only [CollatzResearch.WordTrace]
  refine ⟨5396416888480738169712833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14390445035948635119234221 5396416888480738169712833)
  ·
    refine ⟨4047312666360553627284625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5396416888480738169712833 4047312666360553627284625)
    ·
      refine ⟨3035484499770415220463469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4047312666360553627284625 3035484499770415220463469)
      ·
        refine ⟨1138306687413905707673801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3035484499770415220463469 1138306687413905707673801)
        ·
          refine ⟨853730015560429280755351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1138306687413905707673801 853730015560429280755351)
          ·
            refine ⟨1280595023340643921133027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 853730015560429280755351 1280595023340643921133027)
            ·
              refine ⟨1920892535010965881699541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1280595023340643921133027 1920892535010965881699541)
              ·
                refine ⟨45020918789319512852333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1920892535010965881699541 45020918789319512852333)
                ·
                  rfl

theorem cell21_591826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 7].length) (baseStart_591826 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_591826 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_591826 prefixEnd_591826 := by exact prefixLift 591826
  have htrace : WordTrace (prefixWord ++ tailWord_591826) baseStart_591826 baseEnd_591826 := by
    simpa [prefixWord, tailWord_591826, baseEnd_591826] using wordTrace_append hprefix tailTrace_591826
  have hstable : (prefixWord ++ tailWord_591826).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591826).length < 2 ^ (prefixWord ++ tailWord_591826).sum := by decide
  have hdescent : baseEnd_591826 < baseStart_591826 := by decide
  rcases family_descends (prefixWord ++ tailWord_591826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591857 : List Nat := [1, 2, 2, 2, 5, 2, 1, 1, 5]
def baseStart_591857 : Nat := 118140960795 + 591857 * 2 ^ 59
def prefixEnd_591857 : Nat := 4983230072969 + 3 ^ 40 * 591857 * 2
def baseEnd_591857 : Nat := 135069830990309373540269

theorem tailTrace_591857 : CollatzResearch.WordTrace tailWord_591857 prefixEnd_591857 135069830990309373540269 := by
  unfold tailWord_591857
  simp only [CollatzResearch.WordTrace]
  refine ⟨21586798216810644973229825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14391198811207096648819883 21586798216810644973229825)
  ·
    refine ⟨16190098662607983729922369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21586798216810644973229825 16190098662607983729922369)
    ·
      refine ⟨12142573996955987797441777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16190098662607983729922369 12142573996955987797441777)
      ·
        refine ⟨9106930497716990848081333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12142573996955987797441777 9106930497716990848081333)
        ·
          refine ⟨853774734160967892007625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9106930497716990848081333 853774734160967892007625)
          ·
            refine ⟨640331050620725919005719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 853774734160967892007625 640331050620725919005719)
            ·
              refine ⟨960496575931088878508579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 640331050620725919005719 960496575931088878508579)
              ·
                refine ⟨1440744863896633317762869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 960496575931088878508579 1440744863896633317762869)
                ·
                  refine ⟨135069830990309373540269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1440744863896633317762869 135069830990309373540269)
                  ·
                    rfl

theorem cell21_591857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 1, 5].length) (baseStart_591857 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_591857 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_591857 prefixEnd_591857 := by exact prefixLift 591857
  have htrace : WordTrace (prefixWord ++ tailWord_591857) baseStart_591857 baseEnd_591857 := by
    simpa [prefixWord, tailWord_591857, baseEnd_591857] using wordTrace_append hprefix tailTrace_591857
  have hstable : (prefixWord ++ tailWord_591857).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591857).length < 2 ^ (prefixWord ++ tailWord_591857).sum := by decide
  have hdescent : baseEnd_591857 < baseStart_591857 := by decide
  rcases family_descends (prefixWord ++ tailWord_591857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591908 : List Nat := [2, 3, 1, 4, 3, 1, 2, 2, 3]
def baseStart_591908 : Nat := 118140960795 + 591908 * 2 ^ 59
def prefixEnd_591908 : Nat := 4983230072969 + 3 ^ 40 * 591908 * 2
def baseEnd_591908 : Nat := 135081469885144618190165

theorem tailTrace_591908 : CollatzResearch.WordTrace tailWord_591908 prefixEnd_591908 135081469885144618190165 := by
  unfold tailWord_591908
  simp only [CollatzResearch.WordTrace]
  refine ⟨10794329169812940341668189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14392438893083920455557585 10794329169812940341668189)
  ·
    refine ⟨4047873438679852628125571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10794329169812940341668189 4047873438679852628125571)
    ·
      refine ⟨6071810158019778942188357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4047873438679852628125571 6071810158019778942188357)
      ·
        refine ⟨1138464404628708551660317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6071810158019778942188357 1138464404628708551660317)
        ·
          refine ⟨426924151735765706872619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1138464404628708551660317 426924151735765706872619)
          ·
            refine ⟨640386227603648560308929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 426924151735765706872619 640386227603648560308929)
            ·
              refine ⟨480289670702736420231697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 640386227603648560308929 480289670702736420231697)
              ·
                refine ⟨360217253027052315173773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 480289670702736420231697 360217253027052315173773)
                ·
                  refine ⟨135081469885144618190165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 360217253027052315173773 135081469885144618190165)
                  ·
                    rfl

theorem cell21_591908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 2, 3].length) (baseStart_591908 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_591908 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_591908 prefixEnd_591908 := by exact prefixLift 591908
  have htrace : WordTrace (prefixWord ++ tailWord_591908) baseStart_591908 baseEnd_591908 := by
    simpa [prefixWord, tailWord_591908, baseEnd_591908] using wordTrace_append hprefix tailTrace_591908
  have hstable : (prefixWord ++ tailWord_591908).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591908).length < 2 ^ (prefixWord ++ tailWord_591908).sum := by decide
  have hdescent : baseEnd_591908 < baseStart_591908 := by decide
  rcases family_descends (prefixWord ++ tailWord_591908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591913 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 12]
def baseStart_591913 : Nat := 118140960795 + 591913 * 2 ^ 59
def prefixEnd_591913 : Nat := 4983230072969 + 3 ^ 40 * 591913 * 2
def baseEnd_591913 : Nat := 135082610953265720606821

theorem tailTrace_591913 : CollatzResearch.WordTrace tailWord_591913 prefixEnd_591913 135082610953265720606821 := by
  unfold tailWord_591913
  simp only [CollatzResearch.WordTrace]
  refine ⟨21588840704607766537268393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14392560469738511024845595 21588840704607766537268393)
  ·
    refine ⟨16191630528455824902951295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21588840704607766537268393 16191630528455824902951295)
    ·
      refine ⟨24287445792683737354426943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16191630528455824902951295 24287445792683737354426943)
      ·
        refine ⟨36431168689025606031640415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24287445792683737354426943 36431168689025606031640415)
        ·
          refine ⟨54646753033538409047460623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36431168689025606031640415 54646753033538409047460623)
          ·
            refine ⟨81970129550307613571190935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54646753033538409047460623 81970129550307613571190935)
            ·
              refine ⟨122955194325461420356786403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81970129550307613571190935 122955194325461420356786403)
              ·
                refine ⟨184432791488192130535179605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122955194325461420356786403 184432791488192130535179605)
                ·
                  refine ⟨135082610953265720606821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 184432791488192130535179605 135082610953265720606821)
                  ·
                    rfl

theorem cell21_591913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 12].length) (baseStart_591913 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_591913 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_591913 prefixEnd_591913 := by exact prefixLift 591913
  have htrace : WordTrace (prefixWord ++ tailWord_591913) baseStart_591913 baseEnd_591913 := by
    simpa [prefixWord, tailWord_591913, baseEnd_591913] using wordTrace_append hprefix tailTrace_591913
  have hstable : (prefixWord ++ tailWord_591913).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591913).length < 2 ^ (prefixWord ++ tailWord_591913).sum := by decide
  have hdescent : baseEnd_591913 < baseStart_591913 := by decide
  rcases family_descends (prefixWord ++ tailWord_591913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591964 : List Nat := [2, 2, 4, 1, 1, 4, 1, 2, 4]
def baseStart_591964 : Nat := 118140960795 + 591964 * 2 ^ 59
def prefixEnd_591964 : Nat := 4983230072969 + 3 ^ 40 * 591964 * 2
def baseEnd_591964 : Nat := 135094249848100965256717

theorem tailTrace_591964 : CollatzResearch.WordTrace tailWord_591964 prefixEnd_591964 135094249848100965256717 := by
  unfold tailWord_591964
  simp only [CollatzResearch.WordTrace]
  refine ⟨10795350413711501123687473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14393800551615334831583297 10795350413711501123687473)
  ·
    refine ⟨8096512810283625842765605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10795350413711501123687473 8096512810283625842765605)
    ·
      refine ⟨1518096151928179845518551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8096512810283625842765605 1518096151928179845518551)
      ·
        refine ⟨2277144227892269768277827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1518096151928179845518551 2277144227892269768277827)
        ·
          refine ⟨3415716341838404652416741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2277144227892269768277827 3415716341838404652416741)
          ·
            refine ⟨640446814094700872328139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3415716341838404652416741 640446814094700872328139)
            ·
              refine ⟨960670221142051308492209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 640446814094700872328139 960670221142051308492209)
              ·
                refine ⟨720502665856538481369157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 960670221142051308492209 720502665856538481369157)
                ·
                  refine ⟨135094249848100965256717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 720502665856538481369157 135094249848100965256717)
                  ·
                    rfl

theorem cell21_591964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 2, 4].length) (baseStart_591964 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_591964 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_591964 prefixEnd_591964 := by exact prefixLift 591964
  have htrace : WordTrace (prefixWord ++ tailWord_591964) baseStart_591964 baseEnd_591964 := by
    simpa [prefixWord, tailWord_591964, baseEnd_591964] using wordTrace_append hprefix tailTrace_591964
  have hstable : (prefixWord ++ tailWord_591964).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591964).length < 2 ^ (prefixWord ++ tailWord_591964).sum := by decide
  have hdescent : baseEnd_591964 < baseStart_591964 := by decide
  rcases family_descends (prefixWord ++ tailWord_591964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592026 : List Nat := [3, 1, 1, 5, 3, 1, 1, 1, 5]
def baseStart_592026 : Nat := 118140960795 + 592026 * 2 ^ 59
def prefixEnd_592026 : Nat := 4983230072969 + 3 ^ 40 * 592026 * 2
def baseEnd_592026 : Nat := 135108399092802635223257

theorem tailTrace_592026 : CollatzResearch.WordTrace tailWord_592026 prefixEnd_592026 135108399092802635223257 := by
  unfold tailWord_592026
  simp only [CollatzResearch.WordTrace]
  refine ⟨5398240538299596709032983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14395308102132257890754621 5398240538299596709032983)
  ·
    refine ⟨8097360807449395063549475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5398240538299596709032983 8097360807449395063549475)
    ·
      refine ⟨12146041211174092595324213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8097360807449395063549475 12146041211174092595324213)
      ·
        refine ⟨1138691363547571180811645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12146041211174092595324213 1138691363547571180811645)
        ·
          refine ⟨427009261330339192804367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1138691363547571180811645 427009261330339192804367)
          ·
            refine ⟨640513891995508789206551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 427009261330339192804367 640513891995508789206551)
            ·
              refine ⟨960770837993263183809827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 640513891995508789206551 960770837993263183809827)
              ·
                refine ⟨1441156256989894775714741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 960770837993263183809827 1441156256989894775714741)
                ·
                  refine ⟨135108399092802635223257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1441156256989894775714741 135108399092802635223257)
                  ·
                    rfl

theorem cell21_592026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 1, 5].length) (baseStart_592026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_592026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_592026 prefixEnd_592026 := by exact prefixLift 592026
  have htrace : WordTrace (prefixWord ++ tailWord_592026) baseStart_592026 baseEnd_592026 := by
    simpa [prefixWord, tailWord_592026, baseEnd_592026] using wordTrace_append hprefix tailTrace_592026
  have hstable : (prefixWord ++ tailWord_592026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592026).length < 2 ^ (prefixWord ++ tailWord_592026).sum := by decide
  have hdescent : baseEnd_592026 < baseStart_592026 := by decide
  rcases family_descends (prefixWord ++ tailWord_592026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592178 : List Nat := [3, 2, 1, 1, 5, 2, 1, 3, 3]
def baseStart_592178 : Nat := 118140960795 + 592178 * 2 ^ 59
def prefixEnd_592178 : Nat := 4983230072969 + 3 ^ 40 * 592178 * 2
def baseEnd_592178 : Nat := 135143087563684148689613

theorem tailTrace_592178 : CollatzResearch.WordTrace tailWord_592178 prefixEnd_592178 135143087563684148689613 := by
  unfold tailWord_592178
  simp only [CollatzResearch.WordTrace]
  refine ⟨5399626512161929198916297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14399004032431811197110125 5399626512161929198916297)
  ·
    refine ⟨4049719884121446899187223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5399626512161929198916297 4049719884121446899187223)
    ·
      refine ⟨6074579826182170348780835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4049719884121446899187223 6074579826182170348780835)
      ·
        refine ⟨9111869739273255523171253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6074579826182170348780835 9111869739273255523171253)
        ·
          refine ⟨854237788056867705297305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9111869739273255523171253 854237788056867705297305)
          ·
            refine ⟨640678341042650778972979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 854237788056867705297305 640678341042650778972979)
            ·
              refine ⟨961017511563976168459469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 640678341042650778972979 961017511563976168459469)
              ·
                refine ⟨360381566836491063172301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 961017511563976168459469 360381566836491063172301)
                ·
                  refine ⟨135143087563684148689613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 360381566836491063172301 135143087563684148689613)
                  ·
                    rfl

theorem cell21_592178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 3, 3].length) (baseStart_592178 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_592178 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_592178 prefixEnd_592178 := by exact prefixLift 592178
  have htrace : WordTrace (prefixWord ++ tailWord_592178) baseStart_592178 baseEnd_592178 := by
    simpa [prefixWord, tailWord_592178, baseEnd_592178] using wordTrace_append hprefix tailTrace_592178
  have hstable : (prefixWord ++ tailWord_592178).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592178).length < 2 ^ (prefixWord ++ tailWord_592178).sum := by decide
  have hdescent : baseEnd_592178 < baseStart_592178 := by decide
  rcases family_descends (prefixWord ++ tailWord_592178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592265 : List Nat := [1, 2, 1, 1, 6, 3, 1, 6]
def baseStart_592265 : Nat := 118140960795 + 592265 * 2 ^ 59
def prefixEnd_592265 : Nat := 4983230072969 + 3 ^ 40 * 592265 * 2
def baseEnd_592265 : Nat := 45054314049663776913145

theorem tailTrace_592265 : CollatzResearch.WordTrace tailWord_592265 prefixEnd_592265 45054314049663776913145 := by
  unfold tailWord_592265
  simp only [CollatzResearch.WordTrace]
  refine ⟨21601679199332530654082249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14401119466221687102721499 21601679199332530654082249)
  ·
    refine ⟨16201259399499397990561687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21601679199332530654082249 16201259399499397990561687)
    ·
      refine ⟨24301889099249096985842531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16201259399499397990561687 24301889099249096985842531)
      ·
        refine ⟨36452833648873645478763797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24301889099249096985842531 36452833648873645478763797)
        ·
          refine ⟨1708726577290952131817053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 36452833648873645478763797 1708726577290952131817053)
          ·
            refine ⟨640772466484107049431395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1708726577290952131817053 640772466484107049431395)
            ·
              refine ⟨961158699726160574147093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 640772466484107049431395 961158699726160574147093)
              ·
                refine ⟨45054314049663776913145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 961158699726160574147093 45054314049663776913145)
                ·
                  rfl

theorem cell21_592265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 6].length) (baseStart_592265 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_592265 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_592265 prefixEnd_592265 := by exact prefixLift 592265
  have htrace : WordTrace (prefixWord ++ tailWord_592265) baseStart_592265 baseEnd_592265 := by
    simpa [prefixWord, tailWord_592265, baseEnd_592265] using wordTrace_append hprefix tailTrace_592265
  have hstable : (prefixWord ++ tailWord_592265).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592265).length < 2 ^ (prefixWord ++ tailWord_592265).sum := by decide
  have hdescent : baseEnd_592265 < baseStart_592265 := by decide
  rcases family_descends (prefixWord ++ tailWord_592265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592293 : List Nat := [1, 3, 1, 2, 1, 1, 4, 2, 6]
def baseStart_592293 : Nat := 118140960795 + 592293 * 2 ^ 59
def prefixEnd_592293 : Nat := 4983230072969 + 3 ^ 40 * 592293 * 2
def baseEnd_592293 : Nat := 135169332130469504272711

theorem tailTrace_592293 : CollatzResearch.WordTrace tailWord_592293 prefixEnd_592293 135169332130469504272711 := by
  unfold tailWord_592293
  simp only [CollatzResearch.WordTrace]
  refine ⟨21602700443231091436101533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14401800295487394290734355 21602700443231091436101533)
  ·
    refine ⟨8101012666211659288538075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21602700443231091436101533 8101012666211659288538075)
    ·
      refine ⟨12151518999317488932807113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8101012666211659288538075 12151518999317488932807113)
      ·
        refine ⟨9113639249488116699605335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12151518999317488932807113 9113639249488116699605335)
        ·
          refine ⟨13670458874232175049408003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9113639249488116699605335 13670458874232175049408003)
          ·
            refine ⟨20505688311348262574112005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13670458874232175049408003 20505688311348262574112005)
            ·
              refine ⟨3844816558377799232646001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20505688311348262574112005 3844816558377799232646001)
              ·
                refine ⟨2883612418783349424484501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3844816558377799232646001 2883612418783349424484501)
                ·
                  refine ⟨135169332130469504272711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2883612418783349424484501 135169332130469504272711)
                  ·
                    rfl

theorem cell21_592293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 6].length) (baseStart_592293 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_592293 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_592293 prefixEnd_592293 := by exact prefixLift 592293
  have htrace : WordTrace (prefixWord ++ tailWord_592293) baseStart_592293 baseEnd_592293 := by
    simpa [prefixWord, tailWord_592293, baseEnd_592293] using wordTrace_append hprefix tailTrace_592293
  have hstable : (prefixWord ++ tailWord_592293).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592293).length < 2 ^ (prefixWord ++ tailWord_592293).sum := by decide
  have hdescent : baseEnd_592293 < baseStart_592293 := by decide
  rcases family_descends (prefixWord ++ tailWord_592293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592327 : List Nat := [1, 1, 4, 1, 1, 5, 3, 1, 4]
def baseStart_592327 : Nat := 118140960795 + 592327 * 2 ^ 59
def prefixEnd_592327 : Nat := 4983230072969 + 3 ^ 40 * 592327 * 2
def baseEnd_592327 : Nat := 135177091393693000705975

theorem tailTrace_592327 : CollatzResearch.WordTrace tailWord_592327 prefixEnd_592327 135177091393693000705975 := by
  unfold tailWord_592327
  simp only [CollatzResearch.WordTrace]
  refine ⟨21603940525107915242839235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14402627016738610161892823 21603940525107915242839235)
  ·
    refine ⟨32405910787661872864258853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21603940525107915242839235 32405910787661872864258853)
    ·
      refine ⟨6076108272686601162048535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32405910787661872864258853 6076108272686601162048535)
      ·
        refine ⟨9114162409029901743072803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6076108272686601162048535 9114162409029901743072803)
        ·
          refine ⟨13671243613544852614609205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9114162409029901743072803 13671243613544852614609205)
          ·
            refine ⟨1281679088769829932619613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13671243613544852614609205 1281679088769829932619613)
            ·
              refine ⟨480629658288686224732355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1281679088769829932619613 480629658288686224732355)
              ·
                refine ⟨720944487433029337098533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 480629658288686224732355 720944487433029337098533)
                ·
                  refine ⟨135177091393693000705975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 720944487433029337098533 135177091393693000705975)
                  ·
                    rfl

theorem cell21_592327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 1, 4].length) (baseStart_592327 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_592327 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_592327 prefixEnd_592327 := by exact prefixLift 592327
  have htrace : WordTrace (prefixWord ++ tailWord_592327) baseStart_592327 baseEnd_592327 := by
    simpa [prefixWord, tailWord_592327, baseEnd_592327] using wordTrace_append hprefix tailTrace_592327
  have hstable : (prefixWord ++ tailWord_592327).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592327).length < 2 ^ (prefixWord ++ tailWord_592327).sum := by decide
  have hdescent : baseEnd_592327 < baseStart_592327 := by decide
  rcases family_descends (prefixWord ++ tailWord_592327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592341 : List Nat := [1, 3, 2, 3, 1, 2, 4, 5]
def baseStart_592341 : Nat := 118140960795 + 592341 * 2 ^ 59
def prefixEnd_592341 : Nat := 4983230072969 + 3 ^ 40 * 592341 * 2
def baseEnd_592341 : Nat := 45060095461477362490871

theorem tailTrace_592341 : CollatzResearch.WordTrace tailWord_592341 prefixEnd_592341 45060095461477362490871 := by
  unfold tailWord_592341
  simp only [CollatzResearch.WordTrace]
  refine ⟨21604451147057195633848877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14402967431371463755899251 21604451147057195633848877)
  ·
    refine ⟨8101669180146448362693329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21604451147057195633848877 8101669180146448362693329)
    ·
      refine ⟨6076251885109836272019997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8101669180146448362693329 6076251885109836272019997)
      ·
        refine ⟨2278594456916188602007499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6076251885109836272019997 2278594456916188602007499)
        ·
          refine ⟨3417891685374282903011249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2278594456916188602007499 3417891685374282903011249)
          ·
            refine ⟨2563418764030712177258437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3417891685374282903011249 2563418764030712177258437)
            ·
              refine ⟨480641018255758533235957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2563418764030712177258437 480641018255758533235957)
              ·
                refine ⟨45060095461477362490871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 480641018255758533235957 45060095461477362490871)
                ·
                  rfl

theorem cell21_592341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 5].length) (baseStart_592341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_592341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_592341 prefixEnd_592341 := by exact prefixLift 592341
  have htrace : WordTrace (prefixWord ++ tailWord_592341) baseStart_592341 baseEnd_592341 := by
    simpa [prefixWord, tailWord_592341, baseEnd_592341] using wordTrace_append hprefix tailTrace_592341
  have hstable : (prefixWord ++ tailWord_592341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592341).length < 2 ^ (prefixWord ++ tailWord_592341).sum := by decide
  have hdescent : baseEnd_592341 < baseStart_592341 := by decide
  rcases family_descends (prefixWord ++ tailWord_592341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592369 : List Nat := [1, 2, 2, 2, 3, 1, 1, 3, 6]
def baseStart_592369 : Nat := 118140960795 + 592369 * 2 ^ 59
def prefixEnd_592369 : Nat := 4983230072969 + 3 ^ 40 * 592369 * 2
def baseEnd_592369 : Nat := 135186676365910261005889

theorem tailTrace_592369 : CollatzResearch.WordTrace tailWord_592369 prefixEnd_592369 135186676365910261005889 := by
  unfold tailWord_592369
  simp only [CollatzResearch.WordTrace]
  refine ⟨21605472390955756415868161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14403648260637170943912107 21605472390955756415868161)
  ·
    refine ⟨16204104293216817311901121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21605472390955756415868161 16204104293216817311901121)
    ·
      refine ⟨12153078219912612983925841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16204104293216817311901121 12153078219912612983925841)
      ·
        refine ⟨9114808664934459737944381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12153078219912612983925841 9114808664934459737944381)
        ·
          refine ⟨3418053249350422401729143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9114808664934459737944381 3418053249350422401729143)
          ·
            refine ⟨5127079874025633602593715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3418053249350422401729143 5127079874025633602593715)
            ·
              refine ⟨7690619811038450403890573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5127079874025633602593715 7690619811038450403890573)
              ·
                refine ⟨2883982429139418901458965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7690619811038450403890573 2883982429139418901458965)
                ·
                  refine ⟨135186676365910261005889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2883982429139418901458965 135186676365910261005889)
                  ·
                    rfl

theorem cell21_592369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 6].length) (baseStart_592369 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_592369 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_592369 prefixEnd_592369 := by exact prefixLift 592369
  have htrace : WordTrace (prefixWord ++ tailWord_592369) baseStart_592369 baseEnd_592369 := by
    simpa [prefixWord, tailWord_592369, baseEnd_592369] using wordTrace_append hprefix tailTrace_592369
  have hstable : (prefixWord ++ tailWord_592369).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592369).length < 2 ^ (prefixWord ++ tailWord_592369).sum := by decide
  have hdescent : baseEnd_592369 < baseStart_592369 := by decide
  rcases family_descends (prefixWord ++ tailWord_592369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592420 : List Nat := [2, 3, 1, 5, 1, 1, 2, 2, 4]
def baseStart_592420 : Nat := 118140960795 + 592420 * 2 ^ 59
def prefixEnd_592420 : Nat := 4983230072969 + 3 ^ 40 * 592420 * 2
def baseEnd_592420 : Nat := 135198315260745505655785

theorem tailTrace_592420 : CollatzResearch.WordTrace tailWord_592420 prefixEnd_592420 135198315260745505655785 := by
  unfold tailWord_592420
  simp only [CollatzResearch.WordTrace]
  refine ⟨10803666256885496062987357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14404888342513994750649809 10803666256885496062987357)
  ·
    refine ⟨4051374846332061023620259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10803666256885496062987357 4051374846332061023620259)
    ·
      refine ⟨6077062269498091535430389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4051374846332061023620259 6077062269498091535430389)
      ·
        refine ⟨569724587765446081446599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6077062269498091535430389 569724587765446081446599)
        ·
          refine ⟨854586881648169122169899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 569724587765446081446599 854586881648169122169899)
          ·
            refine ⟨1281880322472253683254849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 854586881648169122169899 1281880322472253683254849)
            ·
              refine ⟨961410241854190262441137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1281880322472253683254849 961410241854190262441137)
              ·
                refine ⟨721057681390642696830853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 961410241854190262441137 721057681390642696830853)
                ·
                  refine ⟨135198315260745505655785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 721057681390642696830853 135198315260745505655785)
                  ·
                    rfl

theorem cell21_592420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 2, 4].length) (baseStart_592420 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_592420 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_592420 prefixEnd_592420 := by exact prefixLift 592420
  have htrace : WordTrace (prefixWord ++ tailWord_592420) baseStart_592420 baseEnd_592420 := by
    simpa [prefixWord, tailWord_592420, baseEnd_592420] using wordTrace_append hprefix tailTrace_592420
  have hstable : (prefixWord ++ tailWord_592420).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592420).length < 2 ^ (prefixWord ++ tailWord_592420).sum := by decide
  have hdescent : baseEnd_592420 < baseStart_592420 := by decide
  rcases family_descends (prefixWord ++ tailWord_592420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592459 : List Nat := [1, 1, 1, 1, 3, 1, 4, 9]
def baseStart_592459 : Nat := 118140960795 + 592459 * 2 ^ 59
def prefixEnd_592459 : Nat := 4983230072969 + 3 ^ 40 * 592459 * 2
def baseEnd_592459 : Nat := 45069071864030034835235

theorem tailTrace_592459 : CollatzResearch.WordTrace tailWord_592459 prefixEnd_592459 45069071864030034835235 := by
  unfold tailWord_592459
  simp only [CollatzResearch.WordTrace]
  refine ⟨21608754960629701786644431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14405836640419801191096287 21608754960629701786644431)
  ·
    refine ⟨32413132440944552679966647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21608754960629701786644431 32413132440944552679966647)
    ·
      refine ⟨48619698661416829019949971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32413132440944552679966647 48619698661416829019949971)
      ·
        refine ⟨72929547992125243529924957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48619698661416829019949971 72929547992125243529924957)
        ·
          refine ⟨27348580497046966323721859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72929547992125243529924957 27348580497046966323721859)
          ·
            refine ⟨41022870745570449485582789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27348580497046966323721859 41022870745570449485582789)
            ·
              refine ⟨7691788264794459278546773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41022870745570449485582789 7691788264794459278546773)
              ·
                refine ⟨45069071864030034835235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7691788264794459278546773 45069071864030034835235)
                ·
                  rfl

theorem cell21_592459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 9].length) (baseStart_592459 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_592459 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_592459 prefixEnd_592459 := by exact prefixLift 592459
  have htrace : WordTrace (prefixWord ++ tailWord_592459) baseStart_592459 baseEnd_592459 := by
    simpa [prefixWord, tailWord_592459, baseEnd_592459] using wordTrace_append hprefix tailTrace_592459
  have hstable : (prefixWord ++ tailWord_592459).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592459).length < 2 ^ (prefixWord ++ tailWord_592459).sum := by decide
  have hdescent : baseEnd_592459 < baseStart_592459 := by decide
  rcases family_descends (prefixWord ++ tailWord_592459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592600 : List Nat := [2, 1, 2, 2, 3, 3, 1, 4, 3]
def baseStart_592600 : Nat := 118140960795 + 592600 * 2 ^ 59
def prefixEnd_592600 : Nat := 4983230072969 + 3 ^ 40 * 592600 * 2
def baseEnd_592600 : Nat := 135239393713105192655417

theorem tailTrace_592600 : CollatzResearch.WordTrace tailWord_592600 prefixEnd_592600 135239393713105192655417 := by
  unfold tailWord_592600
  simp only [CollatzResearch.WordTrace]
  refine ⟨10806948826559441433763627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14409265102079255245018169 10806948826559441433763627)
  ·
    refine ⟨16210423239839162150645441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10806948826559441433763627 16210423239839162150645441)
    ·
      refine ⟨12157817429879371612984081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16210423239839162150645441 12157817429879371612984081)
      ·
        refine ⟨9118363072409528709738061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12157817429879371612984081 9118363072409528709738061)
        ·
          refine ⟨3419386152153573266151773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9118363072409528709738061 3419386152153573266151773)
          ·
            refine ⟨1282269807057589974806915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3419386152153573266151773 1282269807057589974806915)
            ·
              refine ⟨1923404710586384962210373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1282269807057589974806915 1923404710586384962210373)
              ·
                refine ⟨360638383234947180414445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1923404710586384962210373 360638383234947180414445)
                ·
                  refine ⟨135239393713105192655417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 360638383234947180414445 135239393713105192655417)
                  ·
                    rfl

theorem cell21_592600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 4, 3].length) (baseStart_592600 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_592600 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_592600 prefixEnd_592600 := by exact prefixLift 592600
  have htrace : WordTrace (prefixWord ++ tailWord_592600) baseStart_592600 baseEnd_592600 := by
    simpa [prefixWord, tailWord_592600, baseEnd_592600] using wordTrace_append hprefix tailTrace_592600
  have hstable : (prefixWord ++ tailWord_592600).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592600).length < 2 ^ (prefixWord ++ tailWord_592600).sum := by decide
  have hdescent : baseEnd_592600 < baseStart_592600 := by decide
  rcases family_descends (prefixWord ++ tailWord_592600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592659 : List Nat := [1, 1, 1, 2, 1, 3, 3, 6, 3]
def baseStart_592659 : Nat := 118140960795 + 592659 * 2 ^ 59
def prefixEnd_592659 : Nat := 4983230072969 + 3 ^ 40 * 592659 * 2
def baseEnd_592659 : Nat := 135252858316934201171963

theorem tailTrace_592659 : CollatzResearch.WordTrace tailWord_592659 prefixEnd_592659 135252858316934201171963 := by
  unfold tailWord_592659
  simp only [CollatzResearch.WordTrace]
  refine ⟨21616049559905135943925031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14410699706603423962616687 21616049559905135943925031)
  ·
    refine ⟨32424074339857703915887547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21616049559905135943925031 32424074339857703915887547)
    ·
      refine ⟨48636111509786555873831321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32424074339857703915887547 48636111509786555873831321)
      ·
        refine ⟨36477083632339916905373491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48636111509786555873831321 36477083632339916905373491)
        ·
          refine ⟨54715625448509875358060237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36477083632339916905373491 54715625448509875358060237)
          ·
            refine ⟨20518359543191203259272589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54715625448509875358060237 20518359543191203259272589)
            ·
              refine ⟨7694384828696701222227221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20518359543191203259272589 7694384828696701222227221)
              ·
                refine ⟨360674288845157869791901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7694384828696701222227221 360674288845157869791901)
                ·
                  refine ⟨135252858316934201171963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 360674288845157869791901 135252858316934201171963)
                  ·
                    rfl

theorem cell21_592659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 6, 3].length) (baseStart_592659 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_592659 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_592659 prefixEnd_592659 := by exact prefixLift 592659
  have htrace : WordTrace (prefixWord ++ tailWord_592659) baseStart_592659 baseEnd_592659 := by
    simpa [prefixWord, tailWord_592659, baseEnd_592659] using wordTrace_append hprefix tailTrace_592659
  have hstable : (prefixWord ++ tailWord_592659).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592659).length < 2 ^ (prefixWord ++ tailWord_592659).sum := by decide
  have hdescent : baseEnd_592659 < baseStart_592659 := by decide
  rcases family_descends (prefixWord ++ tailWord_592659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592693 : List Nat := [1, 3, 3, 1, 3, 3, 1, 3, 3]
def baseStart_592693 : Nat := 118140960795 + 592693 * 2 ^ 59
def prefixEnd_592693 : Nat := 4983230072969 + 3 ^ 40 * 592693 * 2
def baseEnd_592693 : Nat := 135260617580157697605227

theorem tailTrace_592693 : CollatzResearch.WordTrace tailWord_592693 prefixEnd_592693 135260617580157697605227 := by
  unfold tailWord_592693
  simp only [CollatzResearch.WordTrace]
  refine ⟨21617289641781959750662733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14411526427854639833775155 21617289641781959750662733)
  ·
    refine ⟨8106483615668234906498525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21617289641781959750662733 8106483615668234906498525)
    ·
      refine ⟨3039931355875588089936947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8106483615668234906498525 3039931355875588089936947)
      ·
        refine ⟨4559897033813382134905421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3039931355875588089936947 4559897033813382134905421)
        ·
          refine ⟨1709961387680018300589533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4559897033813382134905421 1709961387680018300589533)
          ·
            refine ⟨641235520380006862721075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1709961387680018300589533 641235520380006862721075)
            ·
              refine ⟨961853280570010294081613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 641235520380006862721075 961853280570010294081613)
              ·
                refine ⟨360694980213753860280605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 961853280570010294081613 360694980213753860280605)
                ·
                  refine ⟨135260617580157697605227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 360694980213753860280605 135260617580157697605227)
                  ·
                    rfl

theorem cell21_592693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 3, 3].length) (baseStart_592693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_592693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_592693 prefixEnd_592693 := by exact prefixLift 592693
  have htrace : WordTrace (prefixWord ++ tailWord_592693) baseStart_592693 baseEnd_592693 := by
    simpa [prefixWord, tailWord_592693, baseEnd_592693] using wordTrace_append hprefix tailTrace_592693
  have hstable : (prefixWord ++ tailWord_592693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592693).length < 2 ^ (prefixWord ++ tailWord_592693).sum := by decide
  have hdescent : baseEnd_592693 < baseStart_592693 := by decide
  rcases family_descends (prefixWord ++ tailWord_592693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592710 : List Nat := [6, 1, 1, 2, 2, 2, 1, 1, 5]
def baseStart_592710 : Nat := 118140960795 + 592710 * 2 ^ 59
def prefixEnd_592710 : Nat := 4983230072969 + 3 ^ 40 * 592710 * 2
def baseEnd_592710 : Nat := 135264497211769445821859

theorem tailTrace_592710 : CollatzResearch.WordTrace tailWord_592710 prefixEnd_592710 135264497211769445821859 := by
  unfold tailWord_592710
  simp only [CollatzResearch.WordTrace]
  refine ⟨675559677585011614188487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14411939788480247769354389 675559677585011614188487)
  ·
    refine ⟨1013339516377517421282731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 675559677585011614188487 1013339516377517421282731)
    ·
      refine ⟨1520009274566276131924097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1013339516377517421282731 1520009274566276131924097)
      ·
        refine ⟨1140006955924707098943073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1520009274566276131924097 1140006955924707098943073)
        ·
          refine ⟨855005216943530324207305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1140006955924707098943073 855005216943530324207305)
          ·
            refine ⟨641253912707647743155479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 855005216943530324207305 641253912707647743155479)
            ·
              refine ⟨961880869061471614733219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 641253912707647743155479 961880869061471614733219)
              ·
                refine ⟨1442821303592207422099829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 961880869061471614733219 1442821303592207422099829)
                ·
                  refine ⟨135264497211769445821859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1442821303592207422099829 135264497211769445821859)
                  ·
                    rfl

theorem cell21_592710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_592710 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_592710 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_592710 prefixEnd_592710 := by exact prefixLift 592710
  have htrace : WordTrace (prefixWord ++ tailWord_592710) baseStart_592710 baseEnd_592710 := by
    simpa [prefixWord, tailWord_592710, baseEnd_592710] using wordTrace_append hprefix tailTrace_592710
  have hstable : (prefixWord ++ tailWord_592710).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592710).length < 2 ^ (prefixWord ++ tailWord_592710).sum := by decide
  have hdescent : baseEnd_592710 < baseStart_592710 := by decide
  rcases family_descends (prefixWord ++ tailWord_592710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592724 : List Nat := [2, 4, 1, 1, 4, 2, 2, 1, 4]
def baseStart_592724 : Nat := 118140960795 + 592724 * 2 ^ 59
def prefixEnd_592724 : Nat := 4983230072969 + 3 ^ 40 * 592724 * 2
def baseEnd_592724 : Nat := 135267692202508532588497

theorem tailTrace_592724 : CollatzResearch.WordTrace tailWord_592724 prefixEnd_592724 135267692202508532588497 := by
  unfold tailWord_592724
  simp only [CollatzResearch.WordTrace]
  refine ⟨10809210152334826022520613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14412280203113101363360817 10809210152334826022520613)
  ·
    refine ⟨2026726903562779879222615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10809210152334826022520613 2026726903562779879222615)
    ·
      refine ⟨3040090355344169818833923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2026726903562779879222615 3040090355344169818833923)
      ·
        refine ⟨4560135533016254728250885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3040090355344169818833923 4560135533016254728250885)
        ·
          refine ⟨855025412440547761547041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4560135533016254728250885 855025412440547761547041)
          ·
            refine ⟨641269059330410821160281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 855025412440547761547041 641269059330410821160281)
            ·
              refine ⟨480951794497808115870211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 641269059330410821160281 480951794497808115870211)
              ·
                refine ⟨721427691746712173805317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 480951794497808115870211 721427691746712173805317)
                ·
                  refine ⟨135267692202508532588497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 721427691746712173805317 135267692202508532588497)
                  ·
                    rfl

theorem cell21_592724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_592724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_592724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_592724 prefixEnd_592724 := by exact prefixLift 592724
  have htrace : WordTrace (prefixWord ++ tailWord_592724) baseStart_592724 baseEnd_592724 := by
    simpa [prefixWord, tailWord_592724, baseEnd_592724] using wordTrace_append hprefix tailTrace_592724
  have hstable : (prefixWord ++ tailWord_592724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592724).length < 2 ^ (prefixWord ++ tailWord_592724).sum := by decide
  have hdescent : baseEnd_592724 < baseStart_592724 := by decide
  rcases family_descends (prefixWord ++ tailWord_592724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592825 : List Nat := [1, 2, 1, 4, 2, 3, 1, 1, 6]
def baseStart_592825 : Nat := 118140960795 + 592825 * 2 ^ 59
def prefixEnd_592825 : Nat := 4983230072969 + 3 ^ 40 * 592825 * 2
def baseEnd_592825 : Nat := 135290741778554801404957

theorem tailTrace_592825 : CollatzResearch.WordTrace tailWord_592825 prefixEnd_592825 135290741778554801404957 := by
  unfold tailWord_592825
  simp only [CollatzResearch.WordTrace]
  refine ⟨21622104077303746294467929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14414736051535830862978619 21622104077303746294467929)
  ·
    refine ⟨16216578057977809720850947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21622104077303746294467929 16216578057977809720850947)
    ·
      refine ⟨24324867086966714581276421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16216578057977809720850947 24324867086966714581276421)
      ·
        refine ⟨4560912578806258983989329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24324867086966714581276421 4560912578806258983989329)
        ·
          refine ⟨3420684434104694237991997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4560912578806258983989329 3420684434104694237991997)
          ·
            refine ⟨1282756662789260339246999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3420684434104694237991997 1282756662789260339246999)
            ·
              refine ⟨1924134994183890508870499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1282756662789260339246999 1924134994183890508870499)
              ·
                refine ⟨2886202491275835763305749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1924134994183890508870499 2886202491275835763305749)
                ·
                  refine ⟨135290741778554801404957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2886202491275835763305749 135290741778554801404957)
                  ·
                    rfl

theorem cell21_592825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 6].length) (baseStart_592825 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_592825 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_592825 prefixEnd_592825 := by exact prefixLift 592825
  have htrace : WordTrace (prefixWord ++ tailWord_592825) baseStart_592825 baseEnd_592825 := by
    simpa [prefixWord, tailWord_592825, baseEnd_592825] using wordTrace_append hprefix tailTrace_592825
  have hstable : (prefixWord ++ tailWord_592825).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592825).length < 2 ^ (prefixWord ++ tailWord_592825).sum := by decide
  have hdescent : baseEnd_592825 < baseStart_592825 := by decide
  rcases family_descends (prefixWord ++ tailWord_592825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592856 : List Nat := [2, 1, 2, 2, 2, 3, 4, 5]
def baseStart_592856 : Nat := 118140960795 + 592856 * 2 ^ 59
def prefixEnd_592856 : Nat := 4983230072969 + 3 ^ 40 * 592856 * 2
def baseEnd_592856 : Nat := 45099272133635212129409

theorem tailTrace_592856 : CollatzResearch.WordTrace tailWord_592856 prefixEnd_592856 45099272133635212129409 := by
  unfold tailWord_592856
  simp only [CollatzResearch.WordTrace]
  refine ⟨10811617370095719294423211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14415489826794292392564281 10811617370095719294423211)
  ·
    refine ⟨16217426055143578941634817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10811617370095719294423211 16217426055143578941634817)
    ·
      refine ⟨12163069541357684206226113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16217426055143578941634817 12163069541357684206226113)
      ·
        refine ⟨9122302156018263154669585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12163069541357684206226113 9122302156018263154669585)
        ·
          refine ⟨6841726617013697366002189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9122302156018263154669585 6841726617013697366002189)
          ·
            refine ⟨2565647481380136512250821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6841726617013697366002189 2565647481380136512250821)
            ·
              refine ⟨481058902758775596047029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2565647481380136512250821 481058902758775596047029)
              ·
                refine ⟨45099272133635212129409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 481058902758775596047029 45099272133635212129409)
                ·
                  rfl

theorem cell21_592856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 5].length) (baseStart_592856 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_592856 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_592856 prefixEnd_592856 := by exact prefixLift 592856
  have htrace : WordTrace (prefixWord ++ tailWord_592856) baseStart_592856 baseEnd_592856 := by
    simpa [prefixWord, tailWord_592856, baseEnd_592856] using wordTrace_append hprefix tailTrace_592856
  have hstable : (prefixWord ++ tailWord_592856).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592856).length < 2 ^ (prefixWord ++ tailWord_592856).sum := by decide
  have hdescent : baseEnd_592856 < baseStart_592856 := by decide
  rcases family_descends (prefixWord ++ tailWord_592856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592901 : List Nat := [1, 3, 1, 1, 2, 3, 3, 3, 4]
def baseStart_592901 : Nat := 118140960795 + 592901 * 2 ^ 59
def prefixEnd_592901 : Nat := 4983230072969 + 3 ^ 40 * 592901 * 2
def baseEnd_592901 : Nat := 135308086013995558138135

theorem tailTrace_592901 : CollatzResearch.WordTrace tailWord_592901 prefixEnd_592901 135308086013995558138135 := by
  unfold tailWord_592901
  simp only [CollatzResearch.WordTrace]
  refine ⟨21624876025028411274234557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14416584016685607516156371 21624876025028411274234557)
  ·
    refine ⟨8109328509385654227837959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21624876025028411274234557 8109328509385654227837959)
    ·
      refine ⟨12163992764078481341756939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8109328509385654227837959 12163992764078481341756939)
      ·
        refine ⟨18245989146117722012635409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12163992764078481341756939 18245989146117722012635409)
        ·
          refine ⟨13684491859588291509476557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18245989146117722012635409 13684491859588291509476557)
          ·
            refine ⟨5131684447345609316053709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13684491859588291509476557 5131684447345609316053709)
            ·
              refine ⟨1924381667754603493520141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5131684447345609316053709 1924381667754603493520141)
              ·
                refine ⟨721643125407976310070053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1924381667754603493520141 721643125407976310070053)
                ·
                  refine ⟨135308086013995558138135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 721643125407976310070053 135308086013995558138135)
                  ·
                    rfl

theorem cell21_592901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 3, 4].length) (baseStart_592901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_592901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_592901 prefixEnd_592901 := by exact prefixLift 592901
  have htrace : WordTrace (prefixWord ++ tailWord_592901) baseStart_592901 baseEnd_592901 := by
    simpa [prefixWord, tailWord_592901, baseEnd_592901] using wordTrace_append hprefix tailTrace_592901
  have hstable : (prefixWord ++ tailWord_592901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592901).length < 2 ^ (prefixWord ++ tailWord_592901).sum := by decide
  have hdescent : baseEnd_592901 < baseStart_592901 := by decide
  rcases family_descends (prefixWord ++ tailWord_592901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592935 : List Nat := [1, 1, 7, 1, 1, 2, 2, 2, 4]
def baseStart_592935 : Nat := 118140960795 + 592935 * 2 ^ 59
def prefixEnd_592935 : Nat := 4983230072969 + 3 ^ 40 * 592935 * 2
def baseEnd_592935 : Nat := 135315845277219054571399

theorem tailTrace_592935 : CollatzResearch.WordTrace tailWord_592935 prefixEnd_592935 135315845277219054571399 := by
  unfold tailWord_592935
  simp only [CollatzResearch.WordTrace]
  refine ⟨21626116106905235080972259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14417410737936823387314839 21626116106905235080972259)
  ·
    refine ⟨32439174160357852621458389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21626116106905235080972259 32439174160357852621458389)
    ·
      refine ⟨760293144383387170815431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 32439174160357852621458389 760293144383387170815431)
      ·
        refine ⟨1140439716575080756223147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 760293144383387170815431 1140439716575080756223147)
        ·
          refine ⟨1710659574862621134334721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1140439716575080756223147 1710659574862621134334721)
          ·
            refine ⟨1282994681146965850751041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1710659574862621134334721 1282994681146965850751041)
            ·
              refine ⟨962246010860224388063281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1282994681146965850751041 962246010860224388063281)
              ·
                refine ⟨721684508145168291047461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 962246010860224388063281 721684508145168291047461)
                ·
                  refine ⟨135315845277219054571399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 721684508145168291047461 135315845277219054571399)
                  ·
                    rfl

theorem cell21_592935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 2, 4].length) (baseStart_592935 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_592935 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_592935 prefixEnd_592935 := by exact prefixLift 592935
  have htrace : WordTrace (prefixWord ++ tailWord_592935) baseStart_592935 baseEnd_592935 := by
    simpa [prefixWord, tailWord_592935, baseEnd_592935] using wordTrace_append hprefix tailTrace_592935
  have hstable : (prefixWord ++ tailWord_592935).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592935).length < 2 ^ (prefixWord ++ tailWord_592935).sum := by decide
  have hdescent : baseEnd_592935 < baseStart_592935 := by decide
  rcases family_descends (prefixWord ++ tailWord_592935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592938 : List Nat := [3, 1, 4, 1, 3, 2, 2, 2, 3]
def baseStart_592938 : Nat := 118140960795 + 592938 * 2 ^ 59
def prefixEnd_592938 : Nat := 4983230072969 + 3 ^ 40 * 592938 * 2
def baseEnd_592938 : Nat := 135316529918091716021393

theorem tailTrace_592938 : CollatzResearch.WordTrace tailWord_592938 prefixEnd_592938 135316529918091716021393 := by
  unfold tailWord_592938
  simp only [CollatzResearch.WordTrace]
  refine ⟨5406556381473591648332867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14417483683929577728887645 5406556381473591648332867)
  ·
    refine ⟨8109834572210387472499301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5406556381473591648332867 8109834572210387472499301)
    ·
      refine ⟨1520593982289447651093619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8109834572210387472499301 1520593982289447651093619)
      ·
        refine ⟨2280890973434171476640429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1520593982289447651093619 2280890973434171476640429)
        ·
          refine ⟨855334115037814303740161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2280890973434171476640429 855334115037814303740161)
          ·
            refine ⟨641500586278360727805121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 855334115037814303740161 641500586278360727805121)
            ·
              refine ⟨481125439708770545853841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 641500586278360727805121 481125439708770545853841)
              ·
                refine ⟨360844079781577909390381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 481125439708770545853841 360844079781577909390381)
                ·
                  refine ⟨135316529918091716021393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 360844079781577909390381 135316529918091716021393)
                  ·
                    rfl

theorem cell21_592938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 2, 3].length) (baseStart_592938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_592938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_592938 prefixEnd_592938 := by exact prefixLift 592938
  have htrace : WordTrace (prefixWord ++ tailWord_592938) baseStart_592938 baseEnd_592938 := by
    simpa [prefixWord, tailWord_592938, baseEnd_592938] using wordTrace_append hprefix tailTrace_592938
  have hstable : (prefixWord ++ tailWord_592938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592938).length < 2 ^ (prefixWord ++ tailWord_592938).sum := by decide
  have hdescent : baseEnd_592938 < baseStart_592938 := by decide
  rcases family_descends (prefixWord ++ tailWord_592938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592946 : List Nat := [3, 2, 1, 1, 2, 2, 2, 3, 5]
def baseStart_592946 : Nat := 118140960795 + 592946 * 2 ^ 59
def prefixEnd_592946 : Nat := 4983230072969 + 3 ^ 40 * 592946 * 2
def baseEnd_592946 : Nat := 135318355627085479888043

theorem tailTrace_592946 : CollatzResearch.WordTrace tailWord_592946 prefixEnd_592946 135318355627085479888043 := by
  unfold tailWord_592946
  simp only [CollatzResearch.WordTrace]
  refine ⟨5406629327466345989905673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14417678206576922639748461 5406629327466345989905673)
  ·
    refine ⟨4054971995599759492429255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5406629327466345989905673 4054971995599759492429255)
    ·
      refine ⟨6082457993399639238643883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4054971995599759492429255 6082457993399639238643883)
      ·
        refine ⟨9123686990099458857965825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6082457993399639238643883 9123686990099458857965825)
        ·
          refine ⟨6842765242574594143474369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9123686990099458857965825 6842765242574594143474369)
          ·
            refine ⟨5132073931930945607605777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6842765242574594143474369 5132073931930945607605777)
            ·
              refine ⟨3849055448948209205704333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5132073931930945607605777 3849055448948209205704333)
              ·
                refine ⟨1443395793355578452139125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3849055448948209205704333 1443395793355578452139125)
                ·
                  refine ⟨135318355627085479888043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1443395793355578452139125 135318355627085479888043)
                  ·
                    rfl

theorem cell21_592946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_592946 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_592946 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_592946 prefixEnd_592946 := by exact prefixLift 592946
  have htrace : WordTrace (prefixWord ++ tailWord_592946) baseStart_592946 baseEnd_592946 := by
    simpa [prefixWord, tailWord_592946, baseEnd_592946] using wordTrace_append hprefix tailTrace_592946
  have hstable : (prefixWord ++ tailWord_592946).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592946).length < 2 ^ (prefixWord ++ tailWord_592946).sum := by decide
  have hdescent : baseEnd_592946 < baseStart_592946 := by decide
  rcases family_descends (prefixWord ++ tailWord_592946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592966 : List Nat := [6, 1, 1, 1, 1, 3, 3, 5]
def baseStart_592966 : Nat := 118140960795 + 592966 * 2 ^ 59
def prefixEnd_592966 : Nat := 4983230072969 + 3 ^ 40 * 592966 * 2
def baseEnd_592966 : Nat := 45107639966523296518223

theorem tailTrace_592966 : CollatzResearch.WordTrace tailWord_592966 prefixEnd_592966 45107639966523296518223 := by
  unfold tailWord_592966
  simp only [CollatzResearch.WordTrace]
  refine ⟨675851461556028980479711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14418164513195284916900501 675851461556028980479711)
  ·
    refine ⟨1013777192334043470719567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 675851461556028980479711 1013777192334043470719567)
    ·
      refine ⟨1520665788501065206079351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1013777192334043470719567 1520665788501065206079351)
      ·
        refine ⟨2280998682751597809119027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1520665788501065206079351 2280998682751597809119027)
        ·
          refine ⟨3421498024127396713678541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2280998682751597809119027 3421498024127396713678541)
          ·
            refine ⟨1283061759047773767629453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3421498024127396713678541 1283061759047773767629453)
            ·
              refine ⟨481148159642915162861045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1283061759047773767629453 481148159642915162861045)
              ·
                refine ⟨45107639966523296518223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 481148159642915162861045 45107639966523296518223)
                ·
                  rfl

theorem cell21_592966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_592966 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_592966 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_592966 prefixEnd_592966 := by exact prefixLift 592966
  have htrace : WordTrace (prefixWord ++ tailWord_592966) baseStart_592966 baseEnd_592966 := by
    simpa [prefixWord, tailWord_592966, baseEnd_592966] using wordTrace_append hprefix tailTrace_592966
  have hstable : (prefixWord ++ tailWord_592966).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592966).length < 2 ^ (prefixWord ++ tailWord_592966).sum := by decide
  have hdescent : baseEnd_592966 < baseStart_592966 := by decide
  rcases family_descends (prefixWord ++ tailWord_592966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592994 : List Nat := [3, 3, 2, 2, 1, 2, 1, 1, 6]
def baseStart_592994 : Nat := 118140960795 + 592994 * 2 ^ 59
def prefixEnd_592994 : Nat := 4983230072969 + 3 ^ 40 * 592994 * 2
def baseEnd_592994 : Nat := 135329309881048063087945

theorem tailTrace_592994 : CollatzResearch.WordTrace tailWord_592994 prefixEnd_592994 135329309881048063087945 := by
  unfold tailWord_592994
  simp only [CollatzResearch.WordTrace]
  refine ⟨5407067003422872039342509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14418845342460992104913357 5407067003422872039342509)
  ·
    refine ⟨2027650126283577014753441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5407067003422872039342509 2027650126283577014753441)
    ·
      refine ⟨1520737594712682761065081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2027650126283577014753441 1520737594712682761065081)
      ·
        refine ⟨1140553196034512070798811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1520737594712682761065081 1140553196034512070798811)
        ·
          refine ⟨1710829794051768106198217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1140553196034512070798811 1710829794051768106198217)
          ·
            refine ⟨1283122345538826079648663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1710829794051768106198217 1283122345538826079648663)
            ·
              refine ⟨1924683518308239119472995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1283122345538826079648663 1924683518308239119472995)
              ·
                refine ⟨2887025277462358679209493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1924683518308239119472995 2887025277462358679209493)
                ·
                  refine ⟨135329309881048063087945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2887025277462358679209493 135329309881048063087945)
                  ·
                    rfl

theorem cell21_592994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_592994 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_592994 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_592994 prefixEnd_592994 := by exact prefixLift 592994
  have htrace : WordTrace (prefixWord ++ tailWord_592994) baseStart_592994 baseEnd_592994 := by
    simpa [prefixWord, tailWord_592994, baseEnd_592994] using wordTrace_append hprefix tailTrace_592994
  have hstable : (prefixWord ++ tailWord_592994).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592994).length < 2 ^ (prefixWord ++ tailWord_592994).sum := by decide
  have hdescent : baseEnd_592994 < baseStart_592994 := by decide
  rcases family_descends (prefixWord ++ tailWord_592994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593025 : List Nat := [1, 2, 4, 2, 2, 3, 2, 5]
def baseStart_593025 : Nat := 118140960795 + 593025 * 2 ^ 59
def prefixEnd_593025 : Nat := 4983230072969 + 3 ^ 40 * 593025 * 2
def baseEnd_593025 : Nat := 45112128167799632690405

theorem tailTrace_593025 : CollatzResearch.WordTrace tailWord_593025 prefixEnd_593025 45112128167799632690405 := by
  unfold tailWord_593025
  simp only [CollatzResearch.WordTrace]
  refine ⟨21629398676579180451748529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14419599117719453634499019 21629398676579180451748529)
  ·
    refine ⟨16222049007434385338811397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21629398676579180451748529 16222049007434385338811397)
    ·
      refine ⟨3041634188893947251027137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16222049007434385338811397 3041634188893947251027137)
      ·
        refine ⟨2281225641670460438270353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3041634188893947251027137 2281225641670460438270353)
        ·
          refine ⟨1710919231252845328702765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2281225641670460438270353 1710919231252845328702765)
          ·
            refine ⟨641594711719816998263537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1710919231252845328702765 641594711719816998263537)
            ·
              refine ⟨481196033789862748697653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 641594711719816998263537 481196033789862748697653)
              ·
                refine ⟨45112128167799632690405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 481196033789862748697653 45112128167799632690405)
                ·
                  rfl

theorem cell21_593025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 5].length) (baseStart_593025 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_593025 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_593025 prefixEnd_593025 := by exact prefixLift 593025
  have htrace : WordTrace (prefixWord ++ tailWord_593025) baseStart_593025 baseEnd_593025 := by
    simpa [prefixWord, tailWord_593025, baseEnd_593025] using wordTrace_append hprefix tailTrace_593025
  have hstable : (prefixWord ++ tailWord_593025).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593025).length < 2 ^ (prefixWord ++ tailWord_593025).sum := by decide
  have hdescent : baseEnd_593025 < baseStart_593025 := by decide
  rcases family_descends (prefixWord ++ tailWord_593025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593053 : List Nat := [1, 4, 2, 1, 1, 2, 2, 4, 4]
def baseStart_593053 : Nat := 118140960795 + 593053 * 2 ^ 59
def prefixEnd_593053 : Nat := 4983230072969 + 3 ^ 40 * 593053 * 2
def baseEnd_593053 : Nat := 135342774484877071604491

theorem tailTrace_593053 : CollatzResearch.WordTrace tailWord_593053 prefixEnd_593053 135342774484877071604491 := by
  unfold tailWord_593053
  simp only [CollatzResearch.WordTrace]
  refine ⟨21630419920477741233767813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14420279946985160822511875 21630419920477741233767813)
  ·
    refine ⟨4055703735089576481331465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21630419920477741233767813 4055703735089576481331465)
    ·
      refine ⟨3041777801317182360998599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4055703735089576481331465 3041777801317182360998599)
      ·
        refine ⟨4562666701975773541497899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3041777801317182360998599 4562666701975773541497899)
        ·
          refine ⟨6844000052963660312246849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4562666701975773541497899 6844000052963660312246849)
          ·
            refine ⟨5133000039722745234185137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6844000052963660312246849 5133000039722745234185137)
            ·
              refine ⟨3849750029792058925638853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5133000039722745234185137 3849750029792058925638853)
              ·
                refine ⟨721828130586011048557285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3849750029792058925638853 721828130586011048557285)
                ·
                  refine ⟨135342774484877071604491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 721828130586011048557285 135342774484877071604491)
                  ·
                    rfl

theorem cell21_593053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_593053 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_593053 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_593053 prefixEnd_593053 := by exact prefixLift 593053
  have htrace : WordTrace (prefixWord ++ tailWord_593053) baseStart_593053 baseEnd_593053 := by
    simpa [prefixWord, tailWord_593053, baseEnd_593053] using wordTrace_append hprefix tailTrace_593053
  have hstable : (prefixWord ++ tailWord_593053).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593053).length < 2 ^ (prefixWord ++ tailWord_593053).sum := by decide
  have hdescent : baseEnd_593053 < baseStart_593053 := by decide
  rcases family_descends (prefixWord ++ tailWord_593053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593056 : List Nat := [2, 1, 1, 4, 2, 1, 5, 2, 3]
def baseStart_593056 : Nat := 118140960795 + 593056 * 2 ^ 59
def prefixEnd_593056 : Nat := 4983230072969 + 3 ^ 40 * 593056 * 2
def baseEnd_593056 : Nat := 135343459125749733054485

theorem tailTrace_593056 : CollatzResearch.WordTrace tailWord_593056 prefixEnd_593056 135343459125749733054485 := by
  unfold tailWord_593056
  simp only [CollatzResearch.WordTrace]
  refine ⟨10815264669733436373063511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14420352892977915164084681 10815264669733436373063511)
  ·
    refine ⟨16222897004600154559595267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10815264669733436373063511 16222897004600154559595267)
    ·
      refine ⟨24334345506900231839392901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16222897004600154559595267 24334345506900231839392901)
      ·
        refine ⟨4562689782543793469886169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24334345506900231839392901 4562689782543793469886169)
        ·
          refine ⟨3422017336907845102414627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4562689782543793469886169 3422017336907845102414627)
          ·
            refine ⟨5133026005361767653621941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3422017336907845102414627 5133026005361767653621941)
            ·
              refine ⟨481221188002665717527057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5133026005361767653621941 481221188002665717527057)
              ·
                refine ⟨360915891001999288145293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 481221188002665717527057 360915891001999288145293)
                ·
                  refine ⟨135343459125749733054485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 360915891001999288145293 135343459125749733054485)
                  ·
                    rfl

theorem cell21_593056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 2, 3].length) (baseStart_593056 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_593056 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_593056 prefixEnd_593056 := by exact prefixLift 593056
  have htrace : WordTrace (prefixWord ++ tailWord_593056) baseStart_593056 baseEnd_593056 := by
    simpa [prefixWord, tailWord_593056, baseEnd_593056] using wordTrace_append hprefix tailTrace_593056
  have hstable : (prefixWord ++ tailWord_593056).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593056).length < 2 ^ (prefixWord ++ tailWord_593056).sum := by decide
  have hdescent : baseEnd_593056 < baseStart_593056 := by decide
  rcases family_descends (prefixWord ++ tailWord_593056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593101 : List Nat := [1, 6, 2, 2, 1, 9]
def baseStart_593101 : Nat := 118140960795 + 593101 * 2 ^ 59
def prefixEnd_593101 : Nat := 4983230072969 + 3 ^ 40 * 593101 * 2
def baseEnd_593101 : Nat := 5013101064401468696459

theorem tailTrace_593101 : CollatzResearch.WordTrace tailWord_593101 prefixEnd_593101 5013101064401468696459 := by
  unfold tailWord_593101
  simp only [CollatzResearch.WordTrace]
  refine ⟨21632170624303845431515157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14421447082869230287676771 21632170624303845431515157)
  ·
    refine ⟨1014007998014242754602273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 21632170624303845431515157 1014007998014242754602273)
    ·
      refine ⟨760505998510682065951705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1014007998014242754602273 760505998510682065951705)
      ·
        refine ⟨570379498883011549463779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 760505998510682065951705 570379498883011549463779)
        ·
          refine ⟨855569248324517324195669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 570379498883011549463779 855569248324517324195669)
          ·
            refine ⟨5013101064401468696459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 855569248324517324195669 5013101064401468696459)
            ·
              rfl

theorem cell21_593101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 9].length) (baseStart_593101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_593101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_593101 prefixEnd_593101 := by exact prefixLift 593101
  have htrace : WordTrace (prefixWord ++ tailWord_593101) baseStart_593101 baseEnd_593101 := by
    simpa [prefixWord, tailWord_593101, baseEnd_593101] using wordTrace_append hprefix tailTrace_593101
  have hstable : (prefixWord ++ tailWord_593101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593101).length < 2 ^ (prefixWord ++ tailWord_593101).sum := by decide
  have hdescent : baseEnd_593101 < baseStart_593101 := by decide
  rcases family_descends (prefixWord ++ tailWord_593101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593157 : List Nat := [1, 3, 1, 1, 2, 1, 3, 2, 7]
def baseStart_593157 : Nat := 118140960795 + 593157 * 2 ^ 59
def prefixEnd_593157 : Nat := 4983230072969 + 3 ^ 40 * 593157 * 2
def baseEnd_593157 : Nat := 135366508701796001870945

theorem tailTrace_593157 : CollatzResearch.WordTrace tailWord_593157 prefixEnd_593157 135366508701796001870945 := by
  unfold tailWord_593157
  simp only [CollatzResearch.WordTrace]
  refine ⟨21634213112100966995553725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14422808741400644663702483 21634213112100966995553725)
  ·
    refine ⟨8112829917037862623332647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21634213112100966995553725 8112829917037862623332647)
    ·
      refine ⟨12169244875556793934998971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8112829917037862623332647 12169244875556793934998971)
      ·
        refine ⟨18253867313335190902498457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12169244875556793934998971 18253867313335190902498457)
        ·
          refine ⟨13690400485001393176873843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18253867313335190902498457 13690400485001393176873843)
          ·
            refine ⟨20535600727502089765310765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13690400485001393176873843 20535600727502089765310765)
            ·
              refine ⟨7700850272813283661991537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20535600727502089765310765 7700850272813283661991537)
              ·
                refine ⟨5775637704609962746493653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7700850272813283661991537 5775637704609962746493653)
                ·
                  refine ⟨135366508701796001870945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5775637704609962746493653 135366508701796001870945)
                  ·
                    rfl

theorem cell21_593157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 7].length) (baseStart_593157 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_593157 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_593157 prefixEnd_593157 := by exact prefixLift 593157
  have htrace : WordTrace (prefixWord ++ tailWord_593157) baseStart_593157 baseEnd_593157 := by
    simpa [prefixWord, tailWord_593157, baseEnd_593157] using wordTrace_append hprefix tailTrace_593157
  have hstable : (prefixWord ++ tailWord_593157).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593157).length < 2 ^ (prefixWord ++ tailWord_593157).sum := by decide
  have hdescent : baseEnd_593157 < baseStart_593157 := by decide
  rcases family_descends (prefixWord ++ tailWord_593157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
