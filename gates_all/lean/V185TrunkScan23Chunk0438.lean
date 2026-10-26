import V185TrunkScan23Chunk0437

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2589653 : List Nat := [1, 3, 2, 3, 4, 1, 1, 1, 2, 1, 4]
def baseStart_2589653 : Nat := 118140960795 + 2589653 * 2 ^ 59
def prefixEnd_2589653 : Nat := 4983230072969 + 3 ^ 40 * 2589653 * 2
def baseEnd_2589653 : Nat := 1329736717357861704427909

theorem tailTrace_2589653 : CollatzResearch.WordTrace tailWord_2589653 prefixEnd_2589653 1329736717357861704427909 := by
  unfold tailWord_2589653
  simp only [CollatzResearch.WordTrace]
  refine ⟨94452404487136933365997613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62968269658091288910665075 94452404487136933365997613)
  ·
    refine ⟨35419651682676350012249105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94452404487136933365997613 35419651682676350012249105)
    ·
      refine ⟨26564738762007262509186829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35419651682676350012249105 26564738762007262509186829)
      ·
        refine ⟨9961777035752723440945061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26564738762007262509186829 9961777035752723440945061)
        ·
          refine ⟨1867833194203635645177199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9961777035752723440945061 1867833194203635645177199)
          ·
            refine ⟨2801749791305453467765799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1867833194203635645177199 2801749791305453467765799)
            ·
              refine ⟨4202624686958180201648699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2801749791305453467765799 4202624686958180201648699)
              ·
                refine ⟨6303937030437270302473049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4202624686958180201648699 6303937030437270302473049)
                ·
                  refine ⟨4727952772827952726854787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6303937030437270302473049 4727952772827952726854787)
                  ·
                    refine ⟨7091929159241929090282181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4727952772827952726854787 7091929159241929090282181)
                    ·
                      refine ⟨1329736717357861704427909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7091929159241929090282181 1329736717357861704427909)
                      ·
                        rfl

theorem cell23_2589653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_2589653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2589653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2589653 prefixEnd_2589653 := by exact prefixLift 2589653
  have htrace : WordTrace (prefixWord ++ tailWord_2589653) baseStart_2589653 baseEnd_2589653 := by
    simpa [prefixWord, tailWord_2589653, baseEnd_2589653] using wordTrace_append hprefix tailTrace_2589653
  have hstable : (prefixWord ++ tailWord_2589653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589653).length < 2 ^ (prefixWord ++ tailWord_2589653).sum := by decide
  have hdescent : baseEnd_2589653 < baseStart_2589653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589656 : List Nat := [2, 1, 2, 2, 2, 5, 1, 1, 2, 2, 3]
def baseStart_2589656 : Nat := 118140960795 + 2589656 * 2 ^ 59
def prefixEnd_2589656 : Nat := 4983230072969 + 3 ^ 40 * 2589656 * 2
def baseEnd_2589656 : Nat := 1329738257799825192690395

theorem tailTrace_2589656 : CollatzResearch.WordTrace tailWord_2589656 prefixEnd_2589656 1329738257799825192690395 := by
  unfold tailWord_2589656
  simp only [CollatzResearch.WordTrace]
  refine ⟨47226256953063032439178411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62968342604084043252237881 47226256953063032439178411)
  ·
    refine ⟨70839385429594548658767617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47226256953063032439178411 70839385429594548658767617)
    ·
      refine ⟨53129539072195911494075713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70839385429594548658767617 53129539072195911494075713)
      ·
        refine ⟨39847154304146933620556785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53129539072195911494075713 39847154304146933620556785)
        ·
          refine ⟨29885365728110200215417589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39847154304146933620556785 29885365728110200215417589)
          ·
            refine ⟨2801753037010331270195399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29885365728110200215417589 2801753037010331270195399)
            ·
              refine ⟨4202629555515496905293099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2801753037010331270195399 4202629555515496905293099)
              ·
                refine ⟨6303944333273245357939649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4202629555515496905293099 6303944333273245357939649)
                ·
                  refine ⟨4727958249954934018454737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6303944333273245357939649 4727958249954934018454737)
                  ·
                    refine ⟨3545968687466200513841053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4727958249954934018454737 3545968687466200513841053)
                    ·
                      refine ⟨1329738257799825192690395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3545968687466200513841053 1329738257799825192690395)
                      ·
                        rfl

theorem cell23_2589656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 1, 2, 2, 3].length) (baseStart_2589656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2589656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2589656 prefixEnd_2589656 := by exact prefixLift 2589656
  have htrace : WordTrace (prefixWord ++ tailWord_2589656) baseStart_2589656 baseEnd_2589656 := by
    simpa [prefixWord, tailWord_2589656, baseEnd_2589656] using wordTrace_append hprefix tailTrace_2589656
  have hstable : (prefixWord ++ tailWord_2589656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589656).length < 2 ^ (prefixWord ++ tailWord_2589656).sum := by decide
  have hdescent : baseEnd_2589656 < baseStart_2589656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589663 : List Nat := [1, 1, 2, 3, 5, 1, 2, 3, 1, 4]
def baseStart_2589663 : Nat := 118140960795 + 2589663 * 2 ^ 59
def prefixEnd_2589663 : Nat := 4983230072969 + 3 ^ 40 * 2589663 * 2
def baseEnd_2589663 : Nat := 443247284054802221767621

theorem tailTrace_2589663 : CollatzResearch.WordTrace tailWord_2589663 prefixEnd_2589663 443247284054802221767621 := by
  unfold tailWord_2589663
  simp only [CollatzResearch.WordTrace]
  refine ⟨94452769217100705073861643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62968512811400470049241095 94452769217100705073861643)
  ·
    refine ⟨141679153825651057610792465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94452769217100705073861643 141679153825651057610792465)
    ·
      refine ⟨106259365369238293208094349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141679153825651057610792465 106259365369238293208094349)
      ·
        refine ⟨39847262013464359953035381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106259365369238293208094349 39847262013464359953035381)
        ·
          refine ⟨3735680813762283745597067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39847262013464359953035381 3735680813762283745597067)
          ·
            refine ⟨5603521220643425618395601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3735680813762283745597067 5603521220643425618395601)
            ·
              refine ⟨4202640915482569213796701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5603521220643425618395601 4202640915482569213796701)
              ·
                refine ⟨1575990343305963455173763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4202640915482569213796701 1575990343305963455173763)
                ·
                  refine ⟨2363985514958945182760645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1575990343305963455173763 2363985514958945182760645)
                  ·
                    refine ⟨443247284054802221767621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2363985514958945182760645 443247284054802221767621)
                    ·
                      rfl

theorem cell23_2589663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 3, 1, 4].length) (baseStart_2589663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2589663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2589663 prefixEnd_2589663 := by exact prefixLift 2589663
  have htrace : WordTrace (prefixWord ++ tailWord_2589663) baseStart_2589663 baseEnd_2589663 := by
    simpa [prefixWord, tailWord_2589663, baseEnd_2589663] using wordTrace_append hprefix tailTrace_2589663
  have hstable : (prefixWord ++ tailWord_2589663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589663).length < 2 ^ (prefixWord ++ tailWord_2589663).sum := by decide
  have hdescent : baseEnd_2589663 < baseStart_2589663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589706 : List Nat := [3, 1, 2, 2, 3, 2, 2, 2, 1, 5]
def baseStart_2589706 : Nat := 118140960795 + 2589706 * 2 ^ 59
def prefixEnd_2589706 : Nat := 4983230072969 + 3 ^ 40 * 2589706 * 2
def baseEnd_2589706 : Nat := 443254643944183332355055

theorem tailTrace_2589706 : CollatzResearch.WordTrace tailWord_2589706 prefixEnd_2589706 443254643944183332355055 := by
  unfold tailWord_2589706
  simp only [CollatzResearch.WordTrace]
  refine ⟨23613584388986230854419243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62969558370629948945117981 23613584388986230854419243)
  ·
    refine ⟨35420376583479346281628865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23613584388986230854419243 35420376583479346281628865)
    ·
      refine ⟨26565282437609509711221649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35420376583479346281628865 26565282437609509711221649)
      ·
        refine ⟨19923961828207132283416237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26565282437609509711221649 19923961828207132283416237)
        ·
          refine ⟨7471485685577674606281089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19923961828207132283416237 7471485685577674606281089)
          ·
            refine ⟨5603614264183255954710817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7471485685577674606281089 5603614264183255954710817)
            ·
              refine ⟨4202710698137441966033113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5603614264183255954710817 4202710698137441966033113)
              ·
                refine ⟨3152033023603081474524835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4202710698137441966033113 3152033023603081474524835)
                ·
                  refine ⟨4728049535404622211787253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3152033023603081474524835 4728049535404622211787253)
                  ·
                    refine ⟨443254643944183332355055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4728049535404622211787253 443254643944183332355055)
                    ·
                      rfl

theorem cell23_2589706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 2, 1, 5].length) (baseStart_2589706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2589706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2589706 prefixEnd_2589706 := by exact prefixLift 2589706
  have htrace : WordTrace (prefixWord ++ tailWord_2589706) baseStart_2589706 baseEnd_2589706 := by
    simpa [prefixWord, tailWord_2589706, baseEnd_2589706] using wordTrace_append hprefix tailTrace_2589706
  have hstable : (prefixWord ++ tailWord_2589706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589706).length < 2 ^ (prefixWord ++ tailWord_2589706).sum := by decide
  have hdescent : baseEnd_2589706 < baseStart_2589706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589714 : List Nat := [3, 2, 5, 1, 1, 2, 1, 3, 1, 4]
def baseStart_2589714 : Nat := 118140960795 + 2589714 * 2 ^ 59
def prefixEnd_2589714 : Nat := 4983230072969 + 3 ^ 40 * 2589714 * 2
def baseEnd_2589714 : Nat := 443256013225928655255043

theorem tailTrace_2589714 : CollatzResearch.WordTrace tailWord_2589714 prefixEnd_2589714 443256013225928655255043 := by
  unfold tailWord_2589714
  simp only [CollatzResearch.WordTrace]
  refine ⟨23613657334978985195992049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62969752893277293855978797 23613657334978985195992049)
  ·
    refine ⟨17710243001234238896994037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23613657334978985195992049 17710243001234238896994037)
    ·
      refine ⟨1660335281365709896593191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17710243001234238896994037 1660335281365709896593191)
      ·
        refine ⟨2490502922048564844889787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1660335281365709896593191 2490502922048564844889787)
        ·
          refine ⟨3735754383072847267334681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2490502922048564844889787 3735754383072847267334681)
          ·
            refine ⟨2801815787304635450501011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3735754383072847267334681 2801815787304635450501011)
            ·
              refine ⟨4202723680956953175751517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2801815787304635450501011 4202723680956953175751517)
              ·
                refine ⟨1576021380358857440906819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4202723680956953175751517 1576021380358857440906819)
                ·
                  refine ⟨2364032070538286161360229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1576021380358857440906819 2364032070538286161360229)
                  ·
                    refine ⟨443256013225928655255043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2364032070538286161360229 443256013225928655255043)
                    ·
                      rfl

theorem cell23_2589714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_2589714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2589714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2589714 prefixEnd_2589714 := by exact prefixLift 2589714
  have htrace : WordTrace (prefixWord ++ tailWord_2589714) baseStart_2589714 baseEnd_2589714 := by
    simpa [prefixWord, tailWord_2589714, baseEnd_2589714] using wordTrace_append hprefix tailTrace_2589714
  have hstable : (prefixWord ++ tailWord_2589714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589714).length < 2 ^ (prefixWord ++ tailWord_2589714).sum := by decide
  have hdescent : baseEnd_2589714 < baseStart_2589714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589720 : List Nat := [2, 1, 2, 3, 2, 4, 1, 3, 1, 1, 3]
def baseStart_2589720 : Nat := 118140960795 + 2589720 * 2 ^ 59
def prefixEnd_2589720 : Nat := 4983230072969 + 3 ^ 40 * 2589720 * 2
def baseEnd_2589720 : Nat := 1329771120561712942290101

theorem tailTrace_2589720 : CollatzResearch.WordTrace tailWord_2589720 prefixEnd_2589720 1329771120561712942290101 := by
  unfold tailWord_2589720
  simp only [CollatzResearch.WordTrace]
  refine ⟨47227424088947101904343307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62969898785262802539124409 47227424088947101904343307)
  ·
    refine ⟨70841136133420652856514961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47227424088947101904343307 70841136133420652856514961)
    ·
      refine ⟨53130852100065489642386221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70841136133420652856514961 53130852100065489642386221)
      ·
        refine ⟨19924069537524558615894833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53130852100065489642386221 19924069537524558615894833)
        ·
          refine ⟨14943052153143418961921125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19924069537524558615894833 14943052153143418961921125)
          ·
            refine ⟨2801822278714391055360211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14943052153143418961921125 2801822278714391055360211)
            ·
              refine ⟨4202733418071586583040317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2801822278714391055360211 4202733418071586583040317)
              ·
                refine ⟨1576025031776844968640119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4202733418071586583040317 1576025031776844968640119)
                ·
                  refine ⟨2364037547665267452960179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1576025031776844968640119 2364037547665267452960179)
                  ·
                    refine ⟨3546056321497901179440269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2364037547665267452960179 3546056321497901179440269)
                    ·
                      refine ⟨1329771120561712942290101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3546056321497901179440269 1329771120561712942290101)
                      ·
                        rfl

theorem cell23_2589720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 3, 1, 1, 3].length) (baseStart_2589720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2589720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2589720 prefixEnd_2589720 := by exact prefixLift 2589720
  have htrace : WordTrace (prefixWord ++ tailWord_2589720) baseStart_2589720 baseEnd_2589720 := by
    simpa [prefixWord, tailWord_2589720, baseEnd_2589720] using wordTrace_append hprefix tailTrace_2589720
  have hstable : (prefixWord ++ tailWord_2589720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589720).length < 2 ^ (prefixWord ++ tailWord_2589720).sum := by decide
  have hdescent : baseEnd_2589720 < baseStart_2589720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589729 : List Nat := [1, 2, 3, 2, 3, 1, 1, 3, 1, 1, 5]
def baseStart_2589729 : Nat := 118140960795 + 2589729 * 2 ^ 59
def prefixEnd_2589729 : Nat := 4983230072969 + 3 ^ 40 * 2589729 * 2
def baseEnd_2589729 : Nat := 1329775741887603407077559

theorem tailTrace_2589729 : CollatzResearch.WordTrace tailWord_2589729 prefixEnd_2589729 1329775741887603407077559 := by
  unfold tailWord_2589729
  simp only [CollatzResearch.WordTrace]
  refine ⟨94455176434861598345764241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62970117623241065563842827 94455176434861598345764241)
  ·
    refine ⟨70841382326146198759323181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94455176434861598345764241 70841382326146198759323181)
    ·
      refine ⟨26565518372304824534746193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70841382326146198759323181 26565518372304824534746193)
      ·
        refine ⟨19924138779228618401059645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26565518372304824534746193 19924138779228618401059645)
        ·
          refine ⟨7471552042210731900397367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19924138779228618401059645 7471552042210731900397367)
          ·
            refine ⟨11207328063316097850596051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7471552042210731900397367 11207328063316097850596051)
            ·
              refine ⟨16810992094974146775894077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11207328063316097850596051 16810992094974146775894077)
              ·
                refine ⟨6304122035615305040960279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16810992094974146775894077 6304122035615305040960279)
                ·
                  refine ⟨9456183053422957561440419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6304122035615305040960279 9456183053422957561440419)
                  ·
                    refine ⟨14184274580134436342160629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9456183053422957561440419 14184274580134436342160629)
                    ·
                      refine ⟨1329775741887603407077559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14184274580134436342160629 1329775741887603407077559)
                      ·
                        rfl

theorem cell23_2589729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_2589729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2589729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2589729 prefixEnd_2589729 := by exact prefixLift 2589729
  have htrace : WordTrace (prefixWord ++ tailWord_2589729) baseStart_2589729 baseEnd_2589729 := by
    simpa [prefixWord, tailWord_2589729, baseEnd_2589729] using wordTrace_append hprefix tailTrace_2589729
  have hstable : (prefixWord ++ tailWord_2589729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589729).length < 2 ^ (prefixWord ++ tailWord_2589729).sum := by decide
  have hdescent : baseEnd_2589729 < baseStart_2589729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589753 : List Nat := [1, 2, 1, 5, 2, 1, 4, 1, 2, 4]
def baseStart_2589753 : Nat := 118140960795 + 2589753 * 2 ^ 59
def prefixEnd_2589753 : Nat := 4983230072969 + 3 ^ 40 * 2589753 * 2
def baseEnd_2589753 : Nat := 443262688474437104392483

theorem tailTrace_2589753 : CollatzResearch.WordTrace tailWord_2589753 prefixEnd_2589753 443262688474437104392483 := by
  unfold tailWord_2589753
  simp only [CollatzResearch.WordTrace]
  refine ⟨94456051786774650444637913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62970701191183100296425275 94456051786774650444637913)
  ·
    refine ⟨70842038840080987833478435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94456051786774650444637913 70842038840080987833478435)
    ·
      refine ⟨106263058260121481750217653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70842038840080987833478435 106263058260121481750217653)
      ·
        refine ⟨9962161711886388914082905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 106263058260121481750217653 9962161711886388914082905)
        ·
          refine ⟨7471621283914791685562179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9962161711886388914082905 7471621283914791685562179)
          ·
            refine ⟨11207431925872187528343269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7471621283914791685562179 11207431925872187528343269)
            ·
              refine ⟨2101393486101035161564363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11207431925872187528343269 2101393486101035161564363)
              ·
                refine ⟨3152090229151552742346545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2101393486101035161564363 3152090229151552742346545)
                ·
                  refine ⟨2364067671863664556759909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3152090229151552742346545 2364067671863664556759909)
                  ·
                    refine ⟨443262688474437104392483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2364067671863664556759909 443262688474437104392483)
                    ·
                      rfl

theorem cell23_2589753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 1, 2, 4].length) (baseStart_2589753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2589753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2589753 prefixEnd_2589753 := by exact prefixLift 2589753
  have htrace : WordTrace (prefixWord ++ tailWord_2589753) baseStart_2589753 baseEnd_2589753 := by
    simpa [prefixWord, tailWord_2589753, baseEnd_2589753] using wordTrace_append hprefix tailTrace_2589753
  have hstable : (prefixWord ++ tailWord_2589753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589753).length < 2 ^ (prefixWord ++ tailWord_2589753).sum := by decide
  have hdescent : baseEnd_2589753 < baseStart_2589753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589759 : List Nat := [1, 1, 2, 2, 3, 1, 1, 5, 1, 3, 3]
def baseStart_2589759 : Nat := 118140960795 + 2589759 * 2 ^ 59
def prefixEnd_2589759 : Nat := 4983230072969 + 3 ^ 40 * 2589759 * 2
def baseEnd_2589759 : Nat := 1329791146307238289702421

theorem tailTrace_2589759 : CollatzResearch.WordTrace tailWord_2589759 prefixEnd_2589759 1329791146307238289702421 := by
  unfold tailWord_2589759
  simp only [CollatzResearch.WordTrace]
  refine ⟨94456270624752913469356331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62970847083168608979570887 94456270624752913469356331)
  ·
    refine ⟨141684405937129370204034497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94456270624752913469356331 141684405937129370204034497)
    ·
      refine ⟨106263304452847027653025873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141684405937129370204034497 106263304452847027653025873)
      ·
        refine ⟨79697478339635270739769405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106263304452847027653025873 79697478339635270739769405)
        ·
          refine ⟨29886554377363226527413527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79697478339635270739769405 29886554377363226527413527)
          ·
            refine ⟨44829831566044839791120291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29886554377363226527413527 44829831566044839791120291)
            ·
              refine ⟨67244747349067259686680437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44829831566044839791120291 67244747349067259686680437)
              ·
                refine ⟨6304195063975055595626291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67244747349067259686680437 6304195063975055595626291)
                ·
                  refine ⟨9456292595962583393439437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6304195063975055595626291 9456292595962583393439437)
                  ·
                    refine ⟨3546109723485968772539789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9456292595962583393439437 3546109723485968772539789)
                    ·
                      refine ⟨1329791146307238289702421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3546109723485968772539789 1329791146307238289702421)
                      ·
                        rfl

theorem cell23_2589759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5, 1, 3, 3].length) (baseStart_2589759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2589759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2589759 prefixEnd_2589759 := by exact prefixLift 2589759
  have htrace : WordTrace (prefixWord ++ tailWord_2589759) baseStart_2589759 baseEnd_2589759 := by
    simpa [prefixWord, tailWord_2589759, baseEnd_2589759] using wordTrace_append hprefix tailTrace_2589759
  have hstable : (prefixWord ++ tailWord_2589759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589759).length < 2 ^ (prefixWord ++ tailWord_2589759).sum := by decide
  have hdescent : baseEnd_2589759 < baseStart_2589759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589766 : List Nat := [6, 1, 1, 1, 1, 2, 2, 9]
def baseStart_2589766 : Nat := 118140960795 + 2589766 * 2 ^ 59
def prefixEnd_2589766 : Nat := 4983230072969 + 3 ^ 40 * 2589766 * 2
def baseEnd_2589766 : Nat := 49251657061919250456107

theorem tailTrace_2589766 : CollatzResearch.WordTrace tailWord_2589766 prefixEnd_2589766 49251657061919250456107 := by
  unfold tailWord_2589766
  simp only [CollatzResearch.WordTrace]
  refine ⟨2951766435491486052026911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 62971017290485035776574101 2951766435491486052026911)
  ·
    refine ⟨4427649653237229078040367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2951766435491486052026911 4427649653237229078040367)
    ·
      refine ⟨6641474479855843617060551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4427649653237229078040367 6641474479855843617060551)
      ·
        refine ⟨9962211719783765425590827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6641474479855843617060551 9962211719783765425590827)
        ·
          refine ⟨14943317579675648138386241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9962211719783765425590827 14943317579675648138386241)
          ·
            refine ⟨11207488184756736103789681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14943317579675648138386241 11207488184756736103789681)
            ·
              refine ⟨8405616138567552077842261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11207488184756736103789681 8405616138567552077842261)
              ·
                refine ⟨49251657061919250456107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8405616138567552077842261 49251657061919250456107)
                ·
                  rfl

theorem cell23_2589766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 9].length) (baseStart_2589766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2589766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2589766 prefixEnd_2589766 := by exact prefixLift 2589766
  have htrace : WordTrace (prefixWord ++ tailWord_2589766) baseStart_2589766 baseEnd_2589766 := by
    simpa [prefixWord, tailWord_2589766, baseEnd_2589766] using wordTrace_append hprefix tailTrace_2589766
  have hstable : (prefixWord ++ tailWord_2589766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589766).length < 2 ^ (prefixWord ++ tailWord_2589766).sum := by decide
  have hdescent : baseEnd_2589766 < baseStart_2589766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589794 : List Nat := [3, 3, 2, 2, 1, 1, 4, 2, 1, 2, 2]
def baseStart_2589794 : Nat := 118140960795 + 2589794 * 2 ^ 59
def prefixEnd_2589794 : Nat := 4983230072969 + 3 ^ 40 * 2589794 * 2
def baseEnd_2589794 : Nat := 1329809118130145652764761

theorem tailTrace_2589794 : CollatzResearch.WordTrace tailWord_2589794 prefixEnd_2589794 1329809118130145652764761 := by
  unfold tailWord_2589794
  simp only [CollatzResearch.WordTrace]
  refine ⟨23614386794906528611720109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62971698119750742964586957 23614386794906528611720109)
  ·
    refine ⟨8855395048089948229395041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23614386794906528611720109 8855395048089948229395041)
    ·
      refine ⟨6641546286067461172046281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8855395048089948229395041 6641546286067461172046281)
      ·
        refine ⟨4981159714550595879034711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6641546286067461172046281 4981159714550595879034711)
        ·
          refine ⟨7471739571825893818552067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4981159714550595879034711 7471739571825893818552067)
          ·
            refine ⟨11207609357738840727828101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7471739571825893818552067 11207609357738840727828101)
            ·
              refine ⟨2101426754576032636467769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11207609357738840727828101 2101426754576032636467769)
              ·
                refine ⟨1576070065932024477350827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2101426754576032636467769 1576070065932024477350827)
                ·
                  refine ⟨2364105098898036716026241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1576070065932024477350827 2364105098898036716026241)
                  ·
                    refine ⟨1773078824173527537019681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2364105098898036716026241 1773078824173527537019681)
                    ·
                      refine ⟨1329809118130145652764761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1773078824173527537019681 1329809118130145652764761)
                      ·
                        rfl

theorem cell23_2589794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_2589794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2589794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2589794 prefixEnd_2589794 := by exact prefixLift 2589794
  have htrace : WordTrace (prefixWord ++ tailWord_2589794) baseStart_2589794 baseEnd_2589794 := by
    simpa [prefixWord, tailWord_2589794, baseEnd_2589794] using wordTrace_append hprefix tailTrace_2589794
  have hstable : (prefixWord ++ tailWord_2589794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589794).length < 2 ^ (prefixWord ++ tailWord_2589794).sum := by decide
  have hdescent : baseEnd_2589794 < baseStart_2589794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589799 : List Nat := [1, 1, 5, 1, 1, 3, 1, 1, 2, 3, 4]
def baseStart_2589799 : Nat := 118140960795 + 2589799 * 2 ^ 59
def prefixEnd_2589799 : Nat := 4983230072969 + 3 ^ 40 * 2589799 * 2
def baseEnd_2589799 : Nat := 1329811685533418133202237

theorem tailTrace_2589799 : CollatzResearch.WordTrace tailWord_2589799 prefixEnd_2589799 1329811685533418133202237 := by
  unfold tailWord_2589799
  simp only [CollatzResearch.WordTrace]
  refine ⟨94457729544608000300812451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62971819696405333533874967 94457729544608000300812451)
  ·
    refine ⟨141686594316912000451218677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94457729544608000300812451 141686594316912000451218677)
    ·
      refine ⟨13283118217210500042301751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 141686594316912000451218677 13283118217210500042301751)
      ·
        refine ⟨19924677325815750063452627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13283118217210500042301751 19924677325815750063452627)
        ·
          refine ⟨29887015988723625095178941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19924677325815750063452627 29887015988723625095178941)
          ·
            refine ⟨11207630995771359410692103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29887015988723625095178941 11207630995771359410692103)
            ·
              refine ⟨16811446493657039116038155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11207630995771359410692103 16811446493657039116038155)
              ·
                refine ⟨25217169740485558674057233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16811446493657039116038155 25217169740485558674057233)
                ·
                  refine ⟨18912877305364169005542925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25217169740485558674057233 18912877305364169005542925)
                  ·
                    refine ⟨7092328989511563377078597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18912877305364169005542925 7092328989511563377078597)
                    ·
                      refine ⟨1329811685533418133202237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7092328989511563377078597 1329811685533418133202237)
                      ·
                        rfl

theorem cell23_2589799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_2589799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2589799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2589799 prefixEnd_2589799 := by exact prefixLift 2589799
  have htrace : WordTrace (prefixWord ++ tailWord_2589799) baseStart_2589799 baseEnd_2589799 := by
    simpa [prefixWord, tailWord_2589799, baseEnd_2589799] using wordTrace_append hprefix tailTrace_2589799
  have hstable : (prefixWord ++ tailWord_2589799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589799).length < 2 ^ (prefixWord ++ tailWord_2589799).sum := by decide
  have hdescent : baseEnd_2589799 < baseStart_2589799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589816 : List Nat := [2, 1, 2, 1, 1, 1, 5, 3, 1, 4, 2]
def baseStart_2589816 : Nat := 118140960795 + 2589816 * 2 ^ 59
def prefixEnd_2589816 : Nat := 4983230072969 + 3 ^ 40 * 2589816 * 2
def baseEnd_2589816 : Nat := 1329820414704544566689659

theorem tailTrace_2589816 : CollatzResearch.WordTrace tailWord_2589816 prefixEnd_2589816 1329820414704544566689659 := by
  unfold tailWord_2589816
  simp only [CollatzResearch.WordTrace]
  refine ⟨47229174792773206102090651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62972233057030941469454201 47229174792773206102090651)
  ·
    refine ⟨70843762189159809153135977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47229174792773206102090651 70843762189159809153135977)
    ·
      refine ⟨53132821641869856864851983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70843762189159809153135977 53132821641869856864851983)
      ·
        refine ⟨79699232462804785297277975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53132821641869856864851983 79699232462804785297277975)
        ·
          refine ⟨119548848694207177945916963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79699232462804785297277975 119548848694207177945916963)
          ·
            refine ⟨179323273041310766918875445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119548848694207177945916963 179323273041310766918875445)
            ·
              refine ⟨16811556847622884398644573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 179323273041310766918875445 16811556847622884398644573)
              ·
                refine ⟨6304333817858581649491715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16811556847622884398644573 6304333817858581649491715)
                ·
                  refine ⟨9456500726787872474237573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6304333817858581649491715 9456500726787872474237573)
                  ·
                    refine ⟨1773093886272726088919545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9456500726787872474237573 1773093886272726088919545)
                    ·
                      refine ⟨1329820414704544566689659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1773093886272726088919545 1329820414704544566689659)
                      ·
                        rfl

theorem cell23_2589816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3, 1, 4, 2].length) (baseStart_2589816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2589816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2589816 prefixEnd_2589816 := by exact prefixLift 2589816
  have htrace : WordTrace (prefixWord ++ tailWord_2589816) baseStart_2589816 baseEnd_2589816 := by
    simpa [prefixWord, tailWord_2589816, baseEnd_2589816] using wordTrace_append hprefix tailTrace_2589816
  have hstable : (prefixWord ++ tailWord_2589816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589816).length < 2 ^ (prefixWord ++ tailWord_2589816).sum := by decide
  have hdescent : baseEnd_2589816 < baseStart_2589816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589850 : List Nat := [3, 1, 1, 5, 1, 2, 1, 1, 4, 2, 2]
def baseStart_2589850 : Nat := 118140960795 + 2589850 * 2 ^ 59
def prefixEnd_2589850 : Nat := 4983230072969 + 3 ^ 40 * 2589850 * 2
def baseEnd_2589850 : Nat := 1329837873046797433664503

theorem tailTrace_2589850 : CollatzResearch.WordTrace tailWord_2589850 prefixEnd_2589850 1329837873046797433664503 := by
  unfold tailWord_2589850
  simp only [CollatzResearch.WordTrace]
  refine ⟨23614897416855809002729751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62973059778282157340612669 23614897416855809002729751)
  ·
    refine ⟨35422346125283713504094627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23614897416855809002729751 35422346125283713504094627)
    ·
      refine ⟨53133519187925570256141941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35422346125283713504094627 53133519187925570256141941)
      ·
        refine ⟨4981267423868022211513307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53133519187925570256141941 4981267423868022211513307)
        ·
          refine ⟨7471901135802033317269961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4981267423868022211513307 7471901135802033317269961)
          ·
            refine ⟨5603925851851524987952471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7471901135802033317269961 5603925851851524987952471)
            ·
              refine ⟨8405888777777287481928707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5603925851851524987952471 8405888777777287481928707)
              ·
                refine ⟨12608833166665931222893061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8405888777777287481928707 12608833166665931222893061)
                ·
                  refine ⟨2364156218749862104292449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12608833166665931222893061 2364156218749862104292449)
                  ·
                    refine ⟨1773117164062396578219337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2364156218749862104292449 1773117164062396578219337)
                    ·
                      refine ⟨1329837873046797433664503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1773117164062396578219337 1329837873046797433664503)
                      ·
                        rfl

theorem cell23_2589850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_2589850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2589850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2589850 prefixEnd_2589850 := by exact prefixLift 2589850
  have htrace : WordTrace (prefixWord ++ tailWord_2589850) baseStart_2589850 baseEnd_2589850 := by
    simpa [prefixWord, tailWord_2589850, baseEnd_2589850] using wordTrace_append hprefix tailTrace_2589850
  have hstable : (prefixWord ++ tailWord_2589850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589850).length < 2 ^ (prefixWord ++ tailWord_2589850).sum := by decide
  have hdescent : baseEnd_2589850 < baseStart_2589850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589856 : List Nat := [2, 1, 1, 4, 2, 1, 1, 6, 5]
def baseStart_2589856 : Nat := 118140960795 + 2589856 * 2 ^ 59
def prefixEnd_2589856 : Nat := 4983230072969 + 3 ^ 40 * 2589856 * 2
def baseEnd_2589856 : Nat := 147760105992302712243275

theorem tailTrace_2589856 : CollatzResearch.WordTrace tailWord_2589856 prefixEnd_2589856 147760105992302712243275 := by
  unfold tailWord_2589856
  simp only [CollatzResearch.WordTrace]
  refine ⟨47229904252700749517818711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62973205670267666023758281 47229904252700749517818711)
  ·
    refine ⟨70844856379051124276728067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47229904252700749517818711 70844856379051124276728067)
    ·
      refine ⟨106267284568576686415092101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70844856379051124276728067 106267284568576686415092101)
      ·
        refine ⟨19925115856608128702829769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106267284568576686415092101 19925115856608128702829769)
        ·
          refine ⟨14943836892456096527122327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19925115856608128702829769 14943836892456096527122327)
          ·
            refine ⟨22415755338684144790683491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14943836892456096527122327 22415755338684144790683491)
            ·
              refine ⟨33623633008026217186025237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22415755338684144790683491 33623633008026217186025237)
              ·
                refine ⟨1576107797251228930594933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33623633008026217186025237 1576107797251228930594933)
                ·
                  refine ⟨147760105992302712243275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1576107797251228930594933 147760105992302712243275)
                  ·
                    rfl

theorem cell23_2589856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 6, 5].length) (baseStart_2589856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2589856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2589856 prefixEnd_2589856 := by exact prefixLift 2589856
  have htrace : WordTrace (prefixWord ++ tailWord_2589856) baseStart_2589856 baseEnd_2589856 := by
    simpa [prefixWord, tailWord_2589856, baseEnd_2589856] using wordTrace_append hprefix tailTrace_2589856
  have hstable : (prefixWord ++ tailWord_2589856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589856).length < 2 ^ (prefixWord ++ tailWord_2589856).sum := by decide
  have hdescent : baseEnd_2589856 < baseStart_2589856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589886 : List Nat := [4, 2, 1, 1, 3, 1, 2, 1, 1, 7]
def baseStart_2589886 : Nat := 118140960795 + 2589886 * 2 ^ 59
def prefixEnd_2589886 : Nat := 4983230072969 + 3 ^ 40 * 2589886 * 2
def baseEnd_2589886 : Nat := 443285452783453097604779

theorem tailTrace_2589886 : CollatzResearch.WordTrace tailWord_2589886 prefixEnd_2589886 443285452783453097604779 := by
  unfold tailWord_2589886
  simp only [CollatzResearch.WordTrace]
  refine ⟨11807612836911601769903689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62973935130195209439486341 11807612836911601769903689)
  ·
    refine ⟨8855709627683701327427767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11807612836911601769903689 8855709627683701327427767)
    ·
      refine ⟨13283564441525551991141651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8855709627683701327427767 13283564441525551991141651)
      ·
        refine ⟨19925346662288327986712477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13283564441525551991141651 19925346662288327986712477)
        ·
          refine ⟨7472004998358122995017179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19925346662288327986712477 7472004998358122995017179)
          ·
            refine ⟨11208007497537184492525769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7472004998358122995017179 11208007497537184492525769)
            ·
              refine ⟨8406005623152888369394327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11208007497537184492525769 8406005623152888369394327)
              ·
                refine ⟨12609008434729332554091491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8406005623152888369394327 12609008434729332554091491)
                ·
                  refine ⟨18913512652093998831137237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12609008434729332554091491 18913512652093998831137237)
                  ·
                    refine ⟨443285452783453097604779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18913512652093998831137237 443285452783453097604779)
                    ·
                      rfl

theorem cell23_2589886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_2589886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2589886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2589886 prefixEnd_2589886 := by exact prefixLift 2589886
  have htrace : WordTrace (prefixWord ++ tailWord_2589886) baseStart_2589886 baseEnd_2589886 := by
    simpa [prefixWord, tailWord_2589886, baseEnd_2589886] using wordTrace_append hprefix tailTrace_2589886
  have hstable : (prefixWord ++ tailWord_2589886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589886).length < 2 ^ (prefixWord ++ tailWord_2589886).sum := by decide
  have hdescent : baseEnd_2589886 < baseStart_2589886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589919 : List Nat := [1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 6]
def baseStart_2589919 : Nat := 118140960795 + 2589919 * 2 ^ 59
def prefixEnd_2589919 : Nat := 4983230072969 + 3 ^ 40 * 2589919 * 2
def baseEnd_2589919 : Nat := 1329873303211957663701685

theorem tailTrace_2589919 : CollatzResearch.WordTrace tailWord_2589919 prefixEnd_2589919 1329873303211957663701685 := by
  unfold tailWord_2589919
  simp only [CollatzResearch.WordTrace]
  refine ⟨94462106304173260795180811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62974737536115507196787207 94462106304173260795180811)
  ·
    refine ⟨141693159456259891192771217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94462106304173260795180811 141693159456259891192771217)
    ·
      refine ⟨106269869592194918394578413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141693159456259891192771217 106269869592194918394578413)
      ·
        refine ⟨39851201097073094397966905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106269869592194918394578413 39851201097073094397966905)
        ·
          refine ⟨29888400822804820798475179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39851201097073094397966905 29888400822804820798475179)
          ·
            refine ⟨44832601234207231197712769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29888400822804820798475179 44832601234207231197712769)
            ·
              refine ⟨33624450925655423398284577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44832601234207231197712769 33624450925655423398284577)
              ·
                refine ⟨25218338194241567548713433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33624450925655423398284577 25218338194241567548713433)
                ·
                  refine ⟨18913753645681175661535075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25218338194241567548713433 18913753645681175661535075)
                  ·
                    refine ⟨28370630468521763492302613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18913753645681175661535075 28370630468521763492302613)
                    ·
                      refine ⟨1329873303211957663701685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28370630468521763492302613 1329873303211957663701685)
                      ·
                        rfl

theorem cell23_2589919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_2589919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2589919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2589919 prefixEnd_2589919 := by exact prefixLift 2589919
  have htrace : WordTrace (prefixWord ++ tailWord_2589919) baseStart_2589919 baseEnd_2589919 := by
    simpa [prefixWord, tailWord_2589919, baseEnd_2589919] using wordTrace_append hprefix tailTrace_2589919
  have hstable : (prefixWord ++ tailWord_2589919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589919).length < 2 ^ (prefixWord ++ tailWord_2589919).sum := by decide
  have hdescent : baseEnd_2589919 < baseStart_2589919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589949 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 3, 1, 8]
def baseStart_2589949 : Nat := 118140960795 + 2589949 * 2 ^ 59
def prefixEnd_2589949 : Nat := 4983230072969 + 3 ^ 40 * 2589949 * 2
def baseEnd_2589949 : Nat := 1329888707631592546326547

theorem tailTrace_2589949 : CollatzResearch.WordTrace tailWord_2589949 prefixEnd_2589949 1329888707631592546326547 := by
  unfold tailWord_2589949
  simp only [CollatzResearch.WordTrace]
  refine ⟨94463200494064575918772901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62975466996043050612515267 94463200494064575918772901)
  ·
    refine ⟨17711850092637107984769919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94463200494064575918772901 17711850092637107984769919)
    ·
      refine ⟨26567775138955661977154879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17711850092637107984769919 26567775138955661977154879)
      ·
        refine ⟨39851662708433492965732319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26567775138955661977154879 39851662708433492965732319)
        ·
          refine ⟨59777494062650239448598479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39851662708433492965732319 59777494062650239448598479)
          ·
            refine ⟨89666241093975359172897719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59777494062650239448598479 89666241093975359172897719)
            ·
              refine ⟨134499361640963038759346579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89666241093975359172897719 134499361640963038759346579)
              ·
                refine ⟨201749042461444558139019869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134499361640963038759346579 201749042461444558139019869)
                ·
                  refine ⟨75655890923041709302132451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 201749042461444558139019869 75655890923041709302132451)
                  ·
                    refine ⟨113483836384562563953198677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 75655890923041709302132451 113483836384562563953198677)
                    ·
                      refine ⟨1329888707631592546326547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 113483836384562563953198677 1329888707631592546326547)
                      ·
                        rfl

theorem cell23_2589949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_2589949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2589949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2589949 prefixEnd_2589949 := by exact prefixLift 2589949
  have htrace : WordTrace (prefixWord ++ tailWord_2589949) baseStart_2589949 baseEnd_2589949 := by
    simpa [prefixWord, tailWord_2589949, baseEnd_2589949] using wordTrace_append hprefix tailTrace_2589949
  have hstable : (prefixWord ++ tailWord_2589949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589949).length < 2 ^ (prefixWord ++ tailWord_2589949).sum := by decide
  have hdescent : baseEnd_2589949 < baseStart_2589949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589973 : List Nat := [1, 3, 2, 1, 2, 1, 1, 5, 3, 1, 3]
def baseStart_2589973 : Nat := 118140960795 + 2589973 * 2 ^ 59
def prefixEnd_2589973 : Nat := 4983230072969 + 3 ^ 40 * 2589973 * 2
def baseEnd_2589973 : Nat := 1329901031167300452426437

theorem tailTrace_2589973 : CollatzResearch.WordTrace tailWord_2589973 prefixEnd_2589973 1329901031167300452426437 := by
  unfold tailWord_2589973
  simp only [CollatzResearch.WordTrace]
  refine ⟨94464075845977628017646573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62976050563985085345097715 94464075845977628017646573)
  ·
    refine ⟨35424028442241610506617465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94464075845977628017646573 35424028442241610506617465)
    ·
      refine ⟨26568021331681207879963099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35424028442241610506617465 26568021331681207879963099)
      ·
        refine ⟨39852031997521811819944649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26568021331681207879963099 39852031997521811819944649)
        ·
          refine ⟨29889023998141358864958487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39852031997521811819944649 29889023998141358864958487)
          ·
            refine ⟨44833535997212038297437731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29889023998141358864958487 44833535997212038297437731)
            ·
              refine ⟨67250303995818057446156597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44833535997212038297437731 67250303995818057446156597)
              ·
                refine ⟨6304715999607942885577181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67250303995818057446156597 6304715999607942885577181)
                ·
                  refine ⟨2364268499852978582091443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6304715999607942885577181 2364268499852978582091443)
                  ·
                    refine ⟨3546402749779467873137165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2364268499852978582091443 3546402749779467873137165)
                    ·
                      refine ⟨1329901031167300452426437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3546402749779467873137165 1329901031167300452426437)
                      ·
                        rfl

theorem cell23_2589973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5, 3, 1, 3].length) (baseStart_2589973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2589973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2589973 prefixEnd_2589973 := by exact prefixLift 2589973
  have htrace : WordTrace (prefixWord ++ tailWord_2589973) baseStart_2589973 baseEnd_2589973 := by
    simpa [prefixWord, tailWord_2589973, baseEnd_2589973] using wordTrace_append hprefix tailTrace_2589973
  have hstable : (prefixWord ++ tailWord_2589973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589973).length < 2 ^ (prefixWord ++ tailWord_2589973).sum := by decide
  have hdescent : baseEnd_2589973 < baseStart_2589973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2589976 : List Nat := [2, 1, 2, 3, 1, 3, 1, 2, 3, 5]
def baseStart_2589976 : Nat := 118140960795 + 2589976 * 2 ^ 59
def prefixEnd_2589976 : Nat := 4983230072969 + 3 ^ 40 * 2589976 * 2
def baseEnd_2589976 : Nat := 443300857203087980229641

theorem tailTrace_2589976 : CollatzResearch.WordTrace tailWord_2589976 prefixEnd_2589976 443300857203087980229641 := by
  unfold tailWord_2589976
  simp only [CollatzResearch.WordTrace]
  refine ⟨47232092632483379765002891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62976123509977839686670521 47232092632483379765002891)
  ·
    refine ⟨70848138948725069647504337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47232092632483379765002891 70848138948725069647504337)
    ·
      refine ⟨53136104211543802235628253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70848138948725069647504337 53136104211543802235628253)
      ·
        refine ⟨19926039079328925838360595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53136104211543802235628253 19926039079328925838360595)
        ·
          refine ⟨29889058618993388757540893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19926039079328925838360595 29889058618993388757540893)
          ·
            refine ⟨11208396982122520784077835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29889058618993388757540893 11208396982122520784077835)
            ·
              refine ⟨16812595473183781176116753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11208396982122520784077835 16812595473183781176116753)
              ·
                refine ⟨12609446604887835882087565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16812595473183781176116753 12609446604887835882087565)
                ·
                  refine ⟨4728542476832938455782837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12609446604887835882087565 4728542476832938455782837)
                  ·
                    refine ⟨443300857203087980229641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4728542476832938455782837 443300857203087980229641)
                    ·
                      rfl

theorem cell23_2589976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 3, 5].length) (baseStart_2589976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2589976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2589976 prefixEnd_2589976 := by exact prefixLift 2589976
  have htrace : WordTrace (prefixWord ++ tailWord_2589976) baseStart_2589976 baseEnd_2589976 := by
    simpa [prefixWord, tailWord_2589976, baseEnd_2589976] using wordTrace_append hprefix tailTrace_2589976
  have hstable : (prefixWord ++ tailWord_2589976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2589976).length < 2 ^ (prefixWord ++ tailWord_2589976).sum := by decide
  have hdescent : baseEnd_2589976 < baseStart_2589976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2589976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590016 : List Nat := [2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 5]
def baseStart_2590016 : Nat := 118140960795 + 2590016 * 2 ^ 59
def prefixEnd_2590016 : Nat := 4983230072969 + 3 ^ 40 * 2590016 * 2
def baseEnd_2590016 : Nat := 1329923110835443784188739

theorem tailTrace_2590016 : CollatzResearch.WordTrace tailWord_2590016 prefixEnd_2590016 1329923110835443784188739 := by
  unfold tailWord_2590016
  simp only [CollatzResearch.WordTrace]
  refine ⟨47232822092410923180730951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62977096123214564240974601 47232822092410923180730951)
  ·
    refine ⟨70849233138616384771096427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47232822092410923180730951 70849233138616384771096427)
    ·
      refine ⟨106273849707924577156644641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70849233138616384771096427 106273849707924577156644641)
      ·
        refine ⟨79705387280943432867483481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106273849707924577156644641 79705387280943432867483481)
        ·
          refine ⟨59779040460707574650612611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79705387280943432867483481 59779040460707574650612611)
          ·
            refine ⟨89668560691061361975918917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59779040460707574650612611 89668560691061361975918917)
            ·
              refine ⟨16812855129574005370484797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89668560691061361975918917 16812855129574005370484797)
              ·
                refine ⟨6304820673590252013931799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16812855129574005370484797 6304820673590252013931799)
                ·
                  refine ⟨9457231010385378020897699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6304820673590252013931799 9457231010385378020897699)
                  ·
                    refine ⟨14185846515578067031346549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9457231010385378020897699 14185846515578067031346549)
                    ·
                      refine ⟨1329923110835443784188739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14185846515578067031346549 1329923110835443784188739)
                      ·
                        rfl

theorem cell23_2590016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 5].length) (baseStart_2590016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2590016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2590016 prefixEnd_2590016 := by exact prefixLift 2590016
  have htrace : WordTrace (prefixWord ++ tailWord_2590016) baseStart_2590016 baseEnd_2590016 := by
    simpa [prefixWord, tailWord_2590016, baseEnd_2590016] using wordTrace_append hprefix tailTrace_2590016
  have hstable : (prefixWord ++ tailWord_2590016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590016).length < 2 ^ (prefixWord ++ tailWord_2590016).sum := by decide
  have hdescent : baseEnd_2590016 < baseStart_2590016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590023 : List Nat := [1, 1, 4, 1, 2, 4, 1, 1, 4, 4]
def baseStart_2590023 : Nat := 118140960795 + 2590023 * 2 ^ 59
def prefixEnd_2590023 : Nat := 4983230072969 + 3 ^ 40 * 2590023 * 2
def baseEnd_2590023 : Nat := 443308901733341752267069

theorem tailTrace_2590023 : CollatzResearch.WordTrace tailWord_2590023 prefixEnd_2590023 443308901733341752267069 := by
  unfold tailWord_2590023
  simp only [CollatzResearch.WordTrace]
  refine ⟨94465899495796486556966723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62977266330530991037977815 94465899495796486556966723)
  ·
    refine ⟨141698849243694729835450085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94465899495796486556966723 141698849243694729835450085)
    ·
      refine ⟨26568534233192761844146891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141698849243694729835450085 26568534233192761844146891)
      ·
        refine ⟨39852801349789142766220337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26568534233192761844146891 39852801349789142766220337)
        ·
          refine ⟨29889601012341857074665253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39852801349789142766220337 29889601012341857074665253)
          ·
            refine ⟨5604300189814098201499735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29889601012341857074665253 5604300189814098201499735)
            ·
              refine ⟨8406450284721147302249603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5604300189814098201499735 8406450284721147302249603)
              ·
                refine ⟨12609675427081720953374405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8406450284721147302249603 12609675427081720953374405)
                ·
                  refine ⟨2364314142577822678757701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12609675427081720953374405 2364314142577822678757701)
                  ·
                    refine ⟨443308901733341752267069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2364314142577822678757701 443308901733341752267069)
                    ·
                      rfl

theorem cell23_2590023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 4, 4].length) (baseStart_2590023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2590023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2590023 prefixEnd_2590023 := by exact prefixLift 2590023
  have htrace : WordTrace (prefixWord ++ tailWord_2590023) baseStart_2590023 baseEnd_2590023 := by
    simpa [prefixWord, tailWord_2590023, baseEnd_2590023] using wordTrace_append hprefix tailTrace_2590023
  have hstable : (prefixWord ++ tailWord_2590023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590023).length < 2 ^ (prefixWord ++ tailWord_2590023).sum := by decide
  have hdescent : baseEnd_2590023 < baseStart_2590023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590026 : List Nat := [3, 1, 2, 1, 1, 1, 1, 4, 3, 2, 4]
def baseStart_2590026 : Nat := 118140960795 + 2590026 * 2 ^ 59
def prefixEnd_2590026 : Nat := 4983230072969 + 3 ^ 40 * 2590026 * 2
def baseEnd_2590026 : Nat := 1329928245641988745063693

theorem tailTrace_2590026 : CollatzResearch.WordTrace tailWord_2590026 prefixEnd_2590026 1329928245641988745063693 := by
  unfold tailWord_2590026
  simp only [CollatzResearch.WordTrace]
  refine ⟨23616502228696404517331483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62977339276523745379550621 23616502228696404517331483)
  ·
    refine ⟨35424753343044606775997225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23616502228696404517331483 35424753343044606775997225)
    ·
      refine ⟨26568565007283455081997919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35424753343044606775997225 26568565007283455081997919)
      ·
        refine ⟨39852847510925182622996879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26568565007283455081997919 39852847510925182622996879)
        ·
          refine ⟨59779271266387773934495319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39852847510925182622996879 59779271266387773934495319)
          ·
            refine ⟨89668906899581660901742979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59779271266387773934495319 89668906899581660901742979)
            ·
              refine ⟨134503360349372491352614469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89668906899581660901742979 134503360349372491352614469)
              ·
                refine ⟨25219380065507342128615213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 134503360349372491352614469 25219380065507342128615213)
                ·
                  refine ⟨9457267524565253298230705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25219380065507342128615213 9457267524565253298230705)
                  ·
                    refine ⟨7092950643423939973673029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9457267524565253298230705 7092950643423939973673029)
                    ·
                      refine ⟨1329928245641988745063693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7092950643423939973673029 1329928245641988745063693)
                      ·
                        rfl

theorem cell23_2590026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_2590026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2590026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2590026 prefixEnd_2590026 := by exact prefixLift 2590026
  have htrace : WordTrace (prefixWord ++ tailWord_2590026) baseStart_2590026 baseEnd_2590026 := by
    simpa [prefixWord, tailWord_2590026, baseEnd_2590026] using wordTrace_append hprefix tailTrace_2590026
  have hstable : (prefixWord ++ tailWord_2590026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590026).length < 2 ^ (prefixWord ++ tailWord_2590026).sum := by decide
  have hdescent : baseEnd_2590026 < baseStart_2590026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590036 : List Nat := [2, 4, 1, 1, 2, 1, 2, 10]
def baseStart_2590036 : Nat := 118140960795 + 2590036 * 2 ^ 59
def prefixEnd_2590036 : Nat := 4983230072969 + 3 ^ 40 * 2590036 * 2
def baseEnd_2590036 : Nat := 49256791868464211331061

theorem tailTrace_2590036 : CollatzResearch.WordTrace tailWord_2590036 prefixEnd_2590036 49256791868464211331061 := by
  unfold tailWord_2590036
  simp only [CollatzResearch.WordTrace]
  refine ⟨47233186822374694888594981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62977582429832926518126641 47233186822374694888594981)
  ·
    refine ⟨8856222529195255291611559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47233186822374694888594981 8856222529195255291611559)
    ·
      refine ⟨13284333793792882937417339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8856222529195255291611559 13284333793792882937417339)
      ·
        refine ⟨19926500690689324406126009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13284333793792882937417339 19926500690689324406126009)
        ·
          refine ⟨14944875518016993304594507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19926500690689324406126009 14944875518016993304594507)
          ·
            refine ⟨22417313277025489956891761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14944875518016993304594507 22417313277025489956891761)
            ·
              refine ⟨16812984957769117467668821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22417313277025489956891761 16812984957769117467668821)
              ·
                refine ⟨49256791868464211331061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 16812984957769117467668821 49256791868464211331061)
                ·
                  rfl

theorem cell23_2590036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 10].length) (baseStart_2590036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2590036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2590036 prefixEnd_2590036 := by exact prefixLift 2590036
  have htrace : WordTrace (prefixWord ++ tailWord_2590036) baseStart_2590036 baseEnd_2590036 := by
    simpa [prefixWord, tailWord_2590036, baseEnd_2590036] using wordTrace_append hprefix tailTrace_2590036
  have hstable : (prefixWord ++ tailWord_2590036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590036).length < 2 ^ (prefixWord ++ tailWord_2590036).sum := by decide
  have hdescent : baseEnd_2590036 < baseStart_2590036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590040 : List Nat := [2, 1, 2, 2, 1, 1, 7, 1, 2, 4]
def baseStart_2590040 : Nat := 118140960795 + 2590040 * 2 ^ 59
def prefixEnd_2590040 : Nat := 4983230072969 + 3 ^ 40 * 2590040 * 2
def baseEnd_2590040 : Nat := 443311811457050563429543

theorem tailTrace_2590040 : CollatzResearch.WordTrace tailWord_2590040 prefixEnd_2590040 443311811457050563429543 := by
  unfold tailWord_2590040
  simp only [CollatzResearch.WordTrace]
  refine ⟨47233259768367449230167787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62977679691156598973557049 47233259768367449230167787)
  ·
    refine ⟨70849889652551173845251681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47233259768367449230167787 70849889652551173845251681)
    ·
      refine ⟨53137417239413380383938761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70849889652551173845251681 53137417239413380383938761)
      ·
        refine ⟨39853062929560035287954071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53137417239413380383938761 39853062929560035287954071)
        ·
          refine ⟨59779594394340052931931107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39853062929560035287954071 59779594394340052931931107)
          ·
            refine ⟨89669391591510079397896661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59779594394340052931931107 89669391591510079397896661)
            ·
              refine ⟨2101626365426017485888203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 89669391591510079397896661 2101626365426017485888203)
              ·
                refine ⟨3152439548139026228832305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2101626365426017485888203 3152439548139026228832305)
                ·
                  refine ⟨2364329661104269671624229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3152439548139026228832305 2364329661104269671624229)
                  ·
                    refine ⟨443311811457050563429543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2364329661104269671624229 443311811457050563429543)
                    ·
                      rfl

theorem cell23_2590040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 1, 2, 4].length) (baseStart_2590040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2590040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2590040 prefixEnd_2590040 := by exact prefixLift 2590040
  have htrace : WordTrace (prefixWord ++ tailWord_2590040) baseStart_2590040 baseEnd_2590040 := by
    simpa [prefixWord, tailWord_2590040, baseEnd_2590040] using wordTrace_append hprefix tailTrace_2590040
  have hstable : (prefixWord ++ tailWord_2590040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590040).length < 2 ^ (prefixWord ++ tailWord_2590040).sum := by decide
  have hdescent : baseEnd_2590040 < baseStart_2590040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590063 : List Nat := [1, 1, 2, 1, 3, 1, 3, 1, 6, 1, 3]
def baseStart_2590063 : Nat := 118140960795 + 2590063 * 2 ^ 59
def prefixEnd_2590063 : Nat := 4983230072969 + 3 ^ 40 * 2590063 * 2
def baseEnd_2590063 : Nat := 1329947244426205100301023

theorem tailTrace_2590063 : CollatzResearch.WordTrace tailWord_2590063 prefixEnd_2590063 1329947244426205100301023 := by
  unfold tailWord_2590063
  simp only [CollatzResearch.WordTrace]
  refine ⟨94467358415651573388422843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62978238943767715592281895 94467358415651573388422843)
  ·
    refine ⟨141701037623477360082634265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94467358415651573388422843 141701037623477360082634265)
    ·
      refine ⟨106275778217608020061975699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141701037623477360082634265 106275778217608020061975699)
      ·
        refine ⟨159413667326412030092963549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106275778217608020061975699 159413667326412030092963549)
        ·
          refine ⟨59780125247404511284861331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159413667326412030092963549 59780125247404511284861331)
          ·
            refine ⟨89670187871106766927291997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59780125247404511284861331 89670187871106766927291997)
            ·
              refine ⟨33626320451665037597734499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89670187871106766927291997 33626320451665037597734499)
              ·
                refine ⟨50439480677497556396601749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33626320451665037597734499 50439480677497556396601749)
                ·
                  refine ⟨2364350656757697956090707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 50439480677497556396601749 2364350656757697956090707)
                  ·
                    refine ⟨3546525985136546934136061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2364350656757697956090707 3546525985136546934136061)
                    ·
                      refine ⟨1329947244426205100301023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3546525985136546934136061 1329947244426205100301023)
                      ·
                        rfl

theorem cell23_2590063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 6, 1, 3].length) (baseStart_2590063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2590063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2590063 prefixEnd_2590063 := by exact prefixLift 2590063
  have htrace : WordTrace (prefixWord ++ tailWord_2590063) baseStart_2590063 baseEnd_2590063 := by
    simpa [prefixWord, tailWord_2590063, baseEnd_2590063] using wordTrace_append hprefix tailTrace_2590063
  have hstable : (prefixWord ++ tailWord_2590063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590063).length < 2 ^ (prefixWord ++ tailWord_2590063).sum := by decide
  have hdescent : baseEnd_2590063 < baseStart_2590063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590076 : List Nat := [2, 2, 2, 1, 1, 1, 3, 2, 2, 2, 5]
def baseStart_2590076 : Nat := 118140960795 + 2590076 * 2 ^ 59
def prefixEnd_2590076 : Nat := 4983230072969 + 3 ^ 40 * 2590076 * 2
def baseEnd_2590076 : Nat := 1329953919674713549438463

theorem tailTrace_2590076 : CollatzResearch.WordTrace tailWord_2590076 prefixEnd_2590076 1329953919674713549438463 := by
  unfold tailWord_2590076
  simp only [CollatzResearch.WordTrace]
  refine ⟨47233916282302238304323041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62978555043069651072430721 47233916282302238304323041)
  ·
    refine ⟨35425437211726678728242281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47233916282302238304323041 35425437211726678728242281)
    ·
      refine ⟨26569077908795009046181711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35425437211726678728242281 26569077908795009046181711)
      ·
        refine ⟨39853616863192513569272567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26569077908795009046181711 39853616863192513569272567)
        ·
          refine ⟨59780425294788770353908851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39853616863192513569272567 59780425294788770353908851)
          ·
            refine ⟨89670637942183155530863277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59780425294788770353908851 89670637942183155530863277)
            ·
              refine ⟨33626489228318683324073729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89670637942183155530863277 33626489228318683324073729)
              ·
                refine ⟨25219866921239012493055297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33626489228318683324073729 25219866921239012493055297)
                ·
                  refine ⟨18914900190929259369791473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25219866921239012493055297 18914900190929259369791473)
                  ·
                    refine ⟨14186175143196944527343605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18914900190929259369791473 14186175143196944527343605)
                    ·
                      refine ⟨1329953919674713549438463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14186175143196944527343605 1329953919674713549438463)
                      ·
                        rfl

theorem cell23_2590076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_2590076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2590076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2590076 prefixEnd_2590076 := by exact prefixLift 2590076
  have htrace : WordTrace (prefixWord ++ tailWord_2590076) baseStart_2590076 baseEnd_2590076 := by
    simpa [prefixWord, tailWord_2590076, baseEnd_2590076] using wordTrace_append hprefix tailTrace_2590076
  have hstable : (prefixWord ++ tailWord_2590076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590076).length < 2 ^ (prefixWord ++ tailWord_2590076).sum := by decide
  have hdescent : baseEnd_2590076 < baseStart_2590076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590081 : List Nat := [1, 2, 4, 3, 3, 1, 1, 1, 3, 2, 2]
def baseStart_2590081 : Nat := 118140960795 + 2590081 * 2 ^ 59
def prefixEnd_2590081 : Nat := 4983230072969 + 3 ^ 40 * 2590081 * 2
def baseEnd_2590081 : Nat := 1329956487077986029875941

theorem tailTrace_2590081 : CollatzResearch.WordTrace tailWord_2590081 prefixEnd_2590081 1329956487077986029875941 := by
  unfold tailWord_2590081
  simp only [CollatzResearch.WordTrace]
  refine ⟨94468014929586362462578097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62978676619724241641718731 94468014929586362462578097)
  ·
    refine ⟨70851011197189771846933573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94468014929586362462578097 70851011197189771846933573)
    ·
      refine ⟨13284564599473082221300045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70851011197189771846933573 13284564599473082221300045)
      ·
        refine ⟨4981711724802405832987517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13284564599473082221300045 4981711724802405832987517)
        ·
          refine ⟨1868141896800902187370319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4981711724802405832987517 1868141896800902187370319)
          ·
            refine ⟨2802212845201353281055479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1868141896800902187370319 2802212845201353281055479)
            ·
              refine ⟨4203319267802029921583219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2802212845201353281055479 4203319267802029921583219)
              ·
                refine ⟨6304978901703044882374829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4203319267802029921583219 6304978901703044882374829)
                ·
                  refine ⟨2364367088138641830890561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6304978901703044882374829 2364367088138641830890561)
                  ·
                    refine ⟨1773275316103981373167921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2364367088138641830890561 1773275316103981373167921)
                    ·
                      refine ⟨1329956487077986029875941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1773275316103981373167921 1329956487077986029875941)
                      ·
                        rfl

theorem cell23_2590081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_2590081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2590081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2590081 prefixEnd_2590081 := by exact prefixLift 2590081
  have htrace : WordTrace (prefixWord ++ tailWord_2590081) baseStart_2590081 baseEnd_2590081 := by
    simpa [prefixWord, tailWord_2590081, baseEnd_2590081] using wordTrace_append hprefix tailTrace_2590081
  have hstable : (prefixWord ++ tailWord_2590081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590081).length < 2 ^ (prefixWord ++ tailWord_2590081).sum := by decide
  have hdescent : baseEnd_2590081 < baseStart_2590081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590136 : List Nat := [2, 1, 2, 1, 2, 2, 2, 1, 1, 2, 7]
def baseStart_2590136 : Nat := 118140960795 + 2590136 * 2 ^ 59
def prefixEnd_2590136 : Nat := 4983230072969 + 3 ^ 40 * 2590136 * 2
def baseEnd_2590136 : Nat := 1329984728513983314688187

theorem tailTrace_2590136 : CollatzResearch.WordTrace tailWord_2590136 prefixEnd_2590136 1329984728513983314688187 := by
  unfold tailWord_2590136
  simp only [CollatzResearch.WordTrace]
  refine ⟨47235010472193553427915131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62980013962924737903886841 47235010472193553427915131)
  ·
    refine ⟨70852515708290330141872697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47235010472193553427915131 70852515708290330141872697)
    ·
      refine ⟨53139386781217747606404523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70852515708290330141872697 53139386781217747606404523)
      ·
        refine ⟨79709080171826621409606785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53139386781217747606404523 79709080171826621409606785)
        ·
          refine ⟨59781810128869966057205089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79709080171826621409606785 59781810128869966057205089)
          ·
            refine ⟨44836357596652474542903817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59781810128869966057205089 44836357596652474542903817)
            ·
              refine ⟨33627268197489355907177863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44836357596652474542903817 33627268197489355907177863)
              ·
                refine ⟨50440902296234033860766795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33627268197489355907177863 50440902296234033860766795)
                ·
                  refine ⟨75661353444351050791150193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50440902296234033860766795 75661353444351050791150193)
                  ·
                    refine ⟨56746015083263288093362645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 75661353444351050791150193 56746015083263288093362645)
                    ·
                      refine ⟨1329984728513983314688187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 56746015083263288093362645 1329984728513983314688187)
                      ·
                        rfl

theorem cell23_2590136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 1, 2, 7].length) (baseStart_2590136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2590136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2590136 prefixEnd_2590136 := by exact prefixLift 2590136
  have htrace : WordTrace (prefixWord ++ tailWord_2590136) baseStart_2590136 baseEnd_2590136 := by
    simpa [prefixWord, tailWord_2590136, baseEnd_2590136] using wordTrace_append hprefix tailTrace_2590136
  have hstable : (prefixWord ++ tailWord_2590136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590136).length < 2 ^ (prefixWord ++ tailWord_2590136).sum := by decide
  have hdescent : baseEnd_2590136 < baseStart_2590136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590203 : List Nat := [1, 1, 1, 1, 1, 3, 2, 2, 7, 4]
def baseStart_2590203 : Nat := 118140960795 + 2590203 * 2 ^ 59
def prefixEnd_2590203 : Nat := 4983230072969 + 3 ^ 40 * 2590203 * 2
def baseEnd_2590203 : Nat := 443339710572611517516793

theorem tailTrace_2590203 : CollatzResearch.WordTrace tailWord_2590203 prefixEnd_2590203 443339710572611517516793 := by
  unfold tailWord_2590203
  simp only [CollatzResearch.WordTrace]
  refine ⟨94472464635144377298519263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62981643090096251532346175 94472464635144377298519263)
  ·
    refine ⟨141708696952716565947778895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94472464635144377298519263 141708696952716565947778895)
    ·
      refine ⟨212563045429074848921668343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141708696952716565947778895 212563045429074848921668343)
      ·
        refine ⟨318844568143612273382502515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212563045429074848921668343 318844568143612273382502515)
        ·
          refine ⟨478266852215418410073753773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318844568143612273382502515 478266852215418410073753773)
          ·
            refine ⟨179350069580781903777657665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 478266852215418410073753773 179350069580781903777657665)
            ·
              refine ⟨134512552185586427833243249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179350069580781903777657665 134512552185586427833243249)
              ·
                refine ⟨100884414139189820874932437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134512552185586427833243249 100884414139189820874932437)
                ·
                  refine ⟨2364478456387261426756229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 100884414139189820874932437 2364478456387261426756229)
                  ·
                    refine ⟨443339710572611517516793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2364478456387261426756229 443339710572611517516793)
                    ·
                      rfl

theorem cell23_2590203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 7, 4].length) (baseStart_2590203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2590203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2590203 prefixEnd_2590203 := by exact prefixLift 2590203
  have htrace : WordTrace (prefixWord ++ tailWord_2590203) baseStart_2590203 baseEnd_2590203 := by
    simpa [prefixWord, tailWord_2590203, baseEnd_2590203] using wordTrace_append hprefix tailTrace_2590203
  have hstable : (prefixWord ++ tailWord_2590203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590203).length < 2 ^ (prefixWord ++ tailWord_2590203).sum := by decide
  have hdescent : baseEnd_2590203 < baseStart_2590203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590250 : List Nat := [3, 1, 4, 1, 1, 1, 2, 4, 6]
def baseStart_2590250 : Nat := 118140960795 + 2590250 * 2 ^ 59
def prefixEnd_2590250 : Nat := 4983230072969 + 3 ^ 40 * 2590250 * 2
def baseEnd_2590250 : Nat := 147782585034288429851407

theorem tailTrace_2590250 : CollatzResearch.WordTrace tailWord_2590250 prefixEnd_2590250 147782585034288429851407 := by
  unfold tailWord_2590250
  simp only [CollatzResearch.WordTrace]
  refine ⟨23618544716493526081370051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62982785910649402883653469 23618544716493526081370051)
  ·
    refine ⟨35427817074740289122055077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23618544716493526081370051 35427817074740289122055077)
    ·
      refine ⟨6642715701513804210385327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35427817074740289122055077 6642715701513804210385327)
      ·
        refine ⟨9964073552270706315577991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6642715701513804210385327 9964073552270706315577991)
        ·
          refine ⟨14946110328406059473366987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9964073552270706315577991 14946110328406059473366987)
          ·
            refine ⟨22419165492609089210050481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14946110328406059473366987 22419165492609089210050481)
            ·
              refine ⟨16814374119456816907537861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22419165492609089210050481 16814374119456816907537861)
              ·
                refine ⟨3152695147398153170163349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16814374119456816907537861 3152695147398153170163349)
                ·
                  refine ⟨147782585034288429851407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3152695147398153170163349 147782585034288429851407)
                  ·
                    rfl

theorem cell23_2590250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 4, 6].length) (baseStart_2590250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2590250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2590250 prefixEnd_2590250 := by exact prefixLift 2590250
  have htrace : WordTrace (prefixWord ++ tailWord_2590250) baseStart_2590250 baseEnd_2590250 := by
    simpa [prefixWord, tailWord_2590250, baseEnd_2590250] using wordTrace_append hprefix tailTrace_2590250
  have hstable : (prefixWord ++ tailWord_2590250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590250).length < 2 ^ (prefixWord ++ tailWord_2590250).sum := by decide
  have hdescent : baseEnd_2590250 < baseStart_2590250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590254 : List Nat := [4, 1, 3, 1, 2, 3, 1, 1, 3, 4]
def baseStart_2590254 : Nat := 118140960795 + 2590254 * 2 ^ 59
def prefixEnd_2590254 : Nat := 4983230072969 + 3 ^ 40 * 2590254 * 2
def baseEnd_2590254 : Nat := 443348439743737951004215

theorem tailTrace_2590254 : CollatzResearch.WordTrace tailWord_2590254 prefixEnd_2590254 443348439743737951004215 := by
  unfold tailWord_2590254
  simp only [CollatzResearch.WordTrace]
  refine ⟨11809290594744951626078227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62982883171973075339083877 11809290594744951626078227)
  ·
    refine ⟨17713935892117427439117341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11809290594744951626078227 17713935892117427439117341)
    ·
      refine ⟨6642725959544035289669003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17713935892117427439117341 6642725959544035289669003)
      ·
        refine ⟨9964088939316052934503505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6642725959544035289669003 9964088939316052934503505)
        ·
          refine ⟨7473066704487039700877629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9964088939316052934503505 7473066704487039700877629)
          ·
            refine ⟨2802400014182639887829111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7473066704487039700877629 2802400014182639887829111)
            ·
              refine ⟨4203600021273959831743667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2802400014182639887829111 4203600021273959831743667)
              ·
                refine ⟨6305400031910939747615501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4203600021273959831743667 6305400031910939747615501)
                ·
                  refine ⟨2364525011966602405355813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6305400031910939747615501 2364525011966602405355813)
                  ·
                    refine ⟨443348439743737951004215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2364525011966602405355813 443348439743737951004215)
                    ·
                      rfl

theorem cell23_2590254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_2590254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2590254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2590254 prefixEnd_2590254 := by exact prefixLift 2590254
  have htrace : WordTrace (prefixWord ++ tailWord_2590254) baseStart_2590254 baseEnd_2590254 := by
    simpa [prefixWord, tailWord_2590254, baseEnd_2590254] using wordTrace_append hprefix tailTrace_2590254
  have hstable : (prefixWord ++ tailWord_2590254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590254).length < 2 ^ (prefixWord ++ tailWord_2590254).sum := by decide
  have hdescent : baseEnd_2590254 < baseStart_2590254 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590311 : List Nat := [1, 1, 5, 1, 1, 1, 6, 2, 1, 1, 3]
def baseStart_2590311 : Nat := 118140960795 + 2590311 * 2 ^ 59
def prefixEnd_2590311 : Nat := 4983230072969 + 3 ^ 40 * 2590311 * 2
def baseEnd_2590311 : Nat := 1330074587628520129999883

theorem tailTrace_2590311 : CollatzResearch.WordTrace tailWord_2590311 prefixEnd_2590311 1330074587628520129999883 := by
  unfold tailWord_2590311
  simp only [CollatzResearch.WordTrace]
  refine ⟨94476403718753111743450787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62984269145835407828967191 94476403718753111743450787)
  ·
    refine ⟨141714605578129667615176181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94476403718753111743450787 141714605578129667615176181)
    ·
      refine ⟨13285744272949656338922767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 141714605578129667615176181 13285744272949656338922767)
      ·
        refine ⟨19928616409424484508384151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13285744272949656338922767 19928616409424484508384151)
        ·
          refine ⟨29892924614136726762576227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19928616409424484508384151 29892924614136726762576227)
          ·
            refine ⟨44839386921205090143864341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29892924614136726762576227 44839386921205090143864341)
            ·
              refine ⟨2101846261931488600493641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 44839386921205090143864341 2101846261931488600493641)
              ·
                refine ⟨1576384696448616450370231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2101846261931488600493641 1576384696448616450370231)
                ·
                  refine ⟨2364577044672924675555347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1576384696448616450370231 2364577044672924675555347)
                  ·
                    refine ⟨3546865567009387013333021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2364577044672924675555347 3546865567009387013333021)
                    ·
                      refine ⟨1330074587628520129999883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3546865567009387013333021 1330074587628520129999883)
                      ·
                        rfl

theorem cell23_2590311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 2, 1, 1, 3].length) (baseStart_2590311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2590311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2590311 prefixEnd_2590311 := by exact prefixLift 2590311
  have htrace : WordTrace (prefixWord ++ tailWord_2590311) baseStart_2590311 baseEnd_2590311 := by
    simpa [prefixWord, tailWord_2590311, baseEnd_2590311] using wordTrace_append hprefix tailTrace_2590311
  have hstable : (prefixWord ++ tailWord_2590311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590311).length < 2 ^ (prefixWord ++ tailWord_2590311).sum := by decide
  have hdescent : baseEnd_2590311 < baseStart_2590311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590313 : List Nat := [1, 2, 1, 1, 1, 4, 2, 1, 3, 1, 6]
def baseStart_2590313 : Nat := 118140960795 + 2590313 * 2 ^ 59
def prefixEnd_2590313 : Nat := 4983230072969 + 3 ^ 40 * 2590313 * 2
def baseEnd_2590313 : Nat := 1330075614589829122174873

theorem tailTrace_2590313 : CollatzResearch.WordTrace tailWord_2590313 prefixEnd_2590313 1330075614589829122174873 := by
  unfold tailWord_2590313
  simp only [CollatzResearch.WordTrace]
  refine ⟨94476476664745866085023593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62984317776497244056682395 94476476664745866085023593)
  ·
    refine ⟨70857357498559399563767695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94476476664745866085023593 70857357498559399563767695)
    ·
      refine ⟨106286036247839099345651543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70857357498559399563767695 106286036247839099345651543)
      ·
        refine ⟨159429054371758649018477315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106286036247839099345651543 159429054371758649018477315)
        ·
          refine ⟨239143581557637973527715973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159429054371758649018477315 239143581557637973527715973)
          ·
            refine ⟨44839421542057120036446745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 239143581557637973527715973 44839421542057120036446745)
            ·
              refine ⟨33629566156542840027335059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44839421542057120036446745 33629566156542840027335059)
              ·
                refine ⟨50444349234814260041002589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33629566156542840027335059 50444349234814260041002589)
                ·
                  refine ⟨18916630963055347515375971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50444349234814260041002589 18916630963055347515375971)
                  ·
                    refine ⟨28374946444583021273063957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18916630963055347515375971 28374946444583021273063957)
                    ·
                      refine ⟨1330075614589829122174873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28374946444583021273063957 1330075614589829122174873)
                      ·
                        rfl

theorem cell23_2590313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 1, 6].length) (baseStart_2590313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2590313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2590313 prefixEnd_2590313 := by exact prefixLift 2590313
  have htrace : WordTrace (prefixWord ++ tailWord_2590313) baseStart_2590313 baseEnd_2590313 := by
    simpa [prefixWord, tailWord_2590313, baseEnd_2590313] using wordTrace_append hprefix tailTrace_2590313
  have hstable : (prefixWord ++ tailWord_2590313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590313).length < 2 ^ (prefixWord ++ tailWord_2590313).sum := by decide
  have hdescent : baseEnd_2590313 < baseStart_2590313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590337 : List Nat := [1, 2, 4, 2, 1, 2, 2, 1, 3, 2, 3]
def baseStart_2590337 : Nat := 118140960795 + 2590337 * 2 ^ 59
def prefixEnd_2590337 : Nat := 4983230072969 + 3 ^ 40 * 2590337 * 2
def baseEnd_2590337 : Nat := 1330087938125537028274763

theorem tailTrace_2590337 : CollatzResearch.WordTrace tailWord_2590337 prefixEnd_2590337 1330087938125537028274763 := by
  unfold tailWord_2590337
  simp only [CollatzResearch.WordTrace]
  refine ⟨94477352016658918183897265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62984901344439278789264843 94477352016658918183897265)
  ·
    refine ⟨70858014012494188637922949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94477352016658918183897265 70858014012494188637922949)
    ·
      refine ⟨13285877627342660369610553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70858014012494188637922949 13285877627342660369610553)
      ·
        refine ⟨9964408220506995277207915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13285877627342660369610553 9964408220506995277207915)
        ·
          refine ⟨14946612330760492915811873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9964408220506995277207915 14946612330760492915811873)
          ·
            refine ⟨11209959248070369686858905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14946612330760492915811873 11209959248070369686858905)
            ·
              refine ⟨8407469436052777265144179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11209959248070369686858905 8407469436052777265144179)
              ·
                refine ⟨12611204154079165897716269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8407469436052777265144179 12611204154079165897716269)
                ·
                  refine ⟨4729201557779687211643601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12611204154079165897716269 4729201557779687211643601)
                  ·
                    refine ⟨3546901168334765408732701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4729201557779687211643601 3546901168334765408732701)
                    ·
                      refine ⟨1330087938125537028274763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3546901168334765408732701 1330087938125537028274763)
                      ·
                        rfl

theorem cell23_2590337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_2590337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2590337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2590337 prefixEnd_2590337 := by exact prefixLift 2590337
  have htrace : WordTrace (prefixWord ++ tailWord_2590337) baseStart_2590337 baseEnd_2590337 := by
    simpa [prefixWord, tailWord_2590337, baseEnd_2590337] using wordTrace_append hprefix tailTrace_2590337
  have hstable : (prefixWord ++ tailWord_2590337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590337).length < 2 ^ (prefixWord ++ tailWord_2590337).sum := by decide
  have hdescent : baseEnd_2590337 < baseStart_2590337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590353 : List Nat := [1, 2, 2, 1, 1, 1, 1, 4, 1, 9]
def baseStart_2590353 : Nat := 118140960795 + 2590353 * 2 ^ 59
def prefixEnd_2590353 : Nat := 4983230072969 + 3 ^ 40 * 2590353 * 2
def baseEnd_2590353 : Nat := 443365384605336321891563

theorem tailTrace_2590353 : CollatzResearch.WordTrace tailWord_2590353 prefixEnd_2590353 443365384605336321891563 := by
  unfold tailWord_2590353
  simp only [CollatzResearch.WordTrace]
  refine ⟨94477935584600952916479713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62985290389733968610986475 94477935584600952916479713)
  ·
    refine ⟨70858451688450714687359785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94477935584600952916479713 70858451688450714687359785)
    ·
      refine ⟨53143838766338036015519839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70858451688450714687359785 53143838766338036015519839)
      ·
        refine ⟨79715758149507054023279759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53143838766338036015519839 79715758149507054023279759)
        ·
          refine ⟨119573637224260581034919639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79715758149507054023279759 119573637224260581034919639)
          ·
            refine ⟨179360455836390871552379459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119573637224260581034919639 179360455836390871552379459)
            ·
              refine ⟨269040683754586307328569189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179360455836390871552379459 269040683754586307328569189)
              ·
                refine ⟨50445128203984932624106723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 269040683754586307328569189 50445128203984932624106723)
                ·
                  refine ⟨75667692305977398936160085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50445128203984932624106723 75667692305977398936160085)
                  ·
                    refine ⟨443365384605336321891563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 75667692305977398936160085 443365384605336321891563)
                    ·
                      rfl

theorem cell23_2590353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 9].length) (baseStart_2590353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2590353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2590353 prefixEnd_2590353 := by exact prefixLift 2590353
  have htrace : WordTrace (prefixWord ++ tailWord_2590353) baseStart_2590353 baseEnd_2590353 := by
    simpa [prefixWord, tailWord_2590353, baseEnd_2590353] using wordTrace_append hprefix tailTrace_2590353
  have hstable : (prefixWord ++ tailWord_2590353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590353).length < 2 ^ (prefixWord ++ tailWord_2590353).sum := by decide
  have hdescent : baseEnd_2590353 < baseStart_2590353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590394 : List Nat := [3, 1, 1, 1, 2, 4, 1, 4, 1, 3, 2]
def baseStart_2590394 : Nat := 118140960795 + 2590394 * 2 ^ 59
def prefixEnd_2590394 : Nat := 4983230072969 + 3 ^ 40 * 2590394 * 2
def baseEnd_2590394 : Nat := 1330117206522843305262001

theorem tailTrace_2590394 : CollatzResearch.WordTrace tailWord_2590394 prefixEnd_2590394 1330117206522843305262001 := by
  unfold tailWord_2590394
  simp only [CollatzResearch.WordTrace]
  refine ⟨23619857744363104229680559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62986287318301611279148157 23619857744363104229680559)
  ·
    refine ⟨35429786616544656344520839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23619857744363104229680559 35429786616544656344520839)
    ·
      refine ⟨53144679924816984516781259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35429786616544656344520839 53144679924816984516781259)
      ·
        refine ⟨79717019887225476775171889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53144679924816984516781259 79717019887225476775171889)
        ·
          refine ⟨59787764915419107581378917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79717019887225476775171889 59787764915419107581378917)
          ·
            refine ⟨11210205921641082671508547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59787764915419107581378917 11210205921641082671508547)
            ·
              refine ⟨16815308882461624007262821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11210205921641082671508547 16815308882461624007262821)
              ·
                refine ⟨3152870415461554501361779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16815308882461624007262821 3152870415461554501361779)
                ·
                  refine ⟨4729305623192331752042669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3152870415461554501361779 4729305623192331752042669)
                  ·
                    refine ⟨1773489608697124407016001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4729305623192331752042669 1773489608697124407016001)
                    ·
                      refine ⟨1330117206522843305262001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1773489608697124407016001 1330117206522843305262001)
                      ·
                        rfl

theorem cell23_2590394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 4, 1, 3, 2].length) (baseStart_2590394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2590394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2590394 prefixEnd_2590394 := by exact prefixLift 2590394
  have htrace : WordTrace (prefixWord ++ tailWord_2590394) baseStart_2590394 baseEnd_2590394 := by
    simpa [prefixWord, tailWord_2590394, baseEnd_2590394] using wordTrace_append hprefix tailTrace_2590394
  have hstable : (prefixWord ++ tailWord_2590394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590394).length < 2 ^ (prefixWord ++ tailWord_2590394).sum := by decide
  have hdescent : baseEnd_2590394 < baseStart_2590394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590407 : List Nat := [1, 1, 4, 1, 1, 1, 4, 1, 3, 4, 2]
def baseStart_2590407 : Nat := 118140960795 + 2590407 * 2 ^ 59
def prefixEnd_2590407 : Nat := 4983230072969 + 3 ^ 40 * 2590407 * 2
def baseEnd_2590407 : Nat := 1330123881771351754399441

theorem tailTrace_2590407 : CollatzResearch.WordTrace tailWord_2590407 prefixEnd_2590407 1330123881771351754399441 := by
  unfold tailWord_2590407
  simp only [CollatzResearch.WordTrace]
  refine ⟨94479905126405320138945475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62986603417603546759296983 94479905126405320138945475)
  ·
    refine ⟨141719857689607980208418213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94479905126405320138945475 141719857689607980208418213)
    ·
      refine ⟨26572473316801496289078415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141719857689607980208418213 26572473316801496289078415)
      ·
        refine ⟨39858709975202244433617623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26572473316801496289078415 39858709975202244433617623)
        ·
          refine ⟨59788064962803366650426435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39858709975202244433617623 59788064962803366650426435)
          ·
            refine ⟨89682097444205049975639653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59788064962803366650426435 89682097444205049975639653)
            ·
              refine ⟨16815393270788446870432435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89682097444205049975639653 16815393270788446870432435)
              ·
                refine ⟨25223089906182670305648653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16815393270788446870432435 25223089906182670305648653)
                ·
                  refine ⟨9458658714818501364618245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25223089906182670305648653 9458658714818501364618245)
                  ·
                    refine ⟨1773498509028469005865921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9458658714818501364618245 1773498509028469005865921)
                    ·
                      refine ⟨1330123881771351754399441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1773498509028469005865921 1330123881771351754399441)
                      ·
                        rfl

theorem cell23_2590407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3, 4, 2].length) (baseStart_2590407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2590407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2590407 prefixEnd_2590407 := by exact prefixLift 2590407
  have htrace : WordTrace (prefixWord ++ tailWord_2590407) baseStart_2590407 baseEnd_2590407 := by
    simpa [prefixWord, tailWord_2590407, baseEnd_2590407] using wordTrace_append hprefix tailTrace_2590407
  have hstable : (prefixWord ++ tailWord_2590407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590407).length < 2 ^ (prefixWord ++ tailWord_2590407).sum := by decide
  have hdescent : baseEnd_2590407 < baseStart_2590407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590424 : List Nat := [2, 1, 2, 2, 3, 1, 1, 3, 4, 2, 2]
def baseStart_2590424 : Nat := 118140960795 + 2590424 * 2 ^ 59
def prefixEnd_2590424 : Nat := 4983230072969 + 3 ^ 40 * 2590424 * 2
def baseEnd_2590424 : Nat := 1330132610942478187886863

theorem tailTrace_2590424 : CollatzResearch.WordTrace tailWord_2590424 prefixEnd_2590424 1330132610942478187886863 := by
  unfold tailWord_2590424
  simp only [CollatzResearch.WordTrace]
  refine ⟨47240262583671866021157163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62987016778229154694876217 47240262583671866021157163)
  ·
    refine ⟨70860393875507799031735745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47240262583671866021157163 70860393875507799031735745)
    ·
      refine ⟨53145295406630849273801809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70860393875507799031735745 53145295406630849273801809)
      ·
        refine ⟨39858971554973136955351357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53145295406630849273801809 39858971554973136955351357)
        ·
          refine ⟨14947114333114926358256759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39858971554973136955351357 14947114333114926358256759)
          ·
            refine ⟨22420671499672389537385139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14947114333114926358256759 22420671499672389537385139)
            ·
              refine ⟨33631007249508584306077709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22420671499672389537385139 33631007249508584306077709)
              ·
                refine ⟨12611627718565719114779141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33631007249508584306077709 12611627718565719114779141)
                ·
                  refine ⟨2364680197231072334021089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12611627718565719114779141 2364680197231072334021089)
                  ·
                    refine ⟨1773510147923304250515817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2364680197231072334021089 1773510147923304250515817)
                    ·
                      refine ⟨1330132610942478187886863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1773510147923304250515817 1330132610942478187886863)
                      ·
                        rfl

theorem cell23_2590424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 4, 2, 2].length) (baseStart_2590424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2590424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2590424 prefixEnd_2590424 := by exact prefixLift 2590424
  have htrace : WordTrace (prefixWord ++ tailWord_2590424) baseStart_2590424 baseEnd_2590424 := by
    simpa [prefixWord, tailWord_2590424, baseEnd_2590424] using wordTrace_append hprefix tailTrace_2590424
  have hstable : (prefixWord ++ tailWord_2590424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590424).length < 2 ^ (prefixWord ++ tailWord_2590424).sum := by decide
  have hdescent : baseEnd_2590424 < baseStart_2590424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590435 : List Nat := [1, 1, 1, 7, 3, 1, 2, 1, 2, 1, 3]
def baseStart_2590435 : Nat := 118140960795 + 2590435 * 2 ^ 59
def prefixEnd_2590435 : Nat := 4983230072969 + 3 ^ 40 * 2590435 * 2
def baseEnd_2590435 : Nat := 1330138259229677644849313

theorem tailTrace_2590435 : CollatzResearch.WordTrace tailWord_2590435 prefixEnd_2590435 1330138259229677644849313 := by
  unfold tailWord_2590435
  simp only [CollatzResearch.WordTrace]
  refine ⟨94480926370303880920964759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62987284246869253947309839 94480926370303880920964759)
  ·
    refine ⟨141721389555455821381447139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94480926370303880920964759 141721389555455821381447139)
    ·
      refine ⟨212582084333183732072170709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141721389555455821381447139 212582084333183732072170709)
      ·
        refine ⟨4982392601558993720441501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 212582084333183732072170709 4982392601558993720441501)
        ·
          refine ⟨1868397225584622645165563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4982392601558993720441501 1868397225584622645165563)
          ·
            refine ⟨2802595838376933967748345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1868397225584622645165563 2802595838376933967748345)
            ·
              refine ⟨2101946878782700475811259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2802595838376933967748345 2101946878782700475811259)
              ·
                refine ⟨3152920318174050713716889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2101946878782700475811259 3152920318174050713716889)
                ·
                  refine ⟨2364690238630538035287667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3152920318174050713716889 2364690238630538035287667)
                  ·
                    refine ⟨3547035357945807052931501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2364690238630538035287667 3547035357945807052931501)
                    ·
                      refine ⟨1330138259229677644849313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3547035357945807052931501 1330138259229677644849313)
                      ·
                        rfl

theorem cell23_2590435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_2590435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2590435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2590435 prefixEnd_2590435 := by exact prefixLift 2590435
  have htrace : WordTrace (prefixWord ++ tailWord_2590435) baseStart_2590435 baseEnd_2590435 := by
    simpa [prefixWord, tailWord_2590435, baseEnd_2590435] using wordTrace_append hprefix tailTrace_2590435
  have hstable : (prefixWord ++ tailWord_2590435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590435).length < 2 ^ (prefixWord ++ tailWord_2590435).sum := by decide
  have hdescent : baseEnd_2590435 < baseStart_2590435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590470 : List Nat := [6, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2]
def baseStart_2590470 : Nat := 118140960795 + 2590470 * 2 ^ 59
def prefixEnd_2590470 : Nat := 4983230072969 + 3 ^ 40 * 2590470 * 2
def baseEnd_2590470 : Nat := 1330156231052585007911653

theorem tailTrace_2590470 : CollatzResearch.WordTrace tailWord_2590470 prefixEnd_2590470 1330156231052585007911653 := by
  unfold tailWord_2590470
  simp only [CollatzResearch.WordTrace]
  refine ⟨2952568841411783809327777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 62988135283451387932325909 2952568841411783809327777)
  ·
    refine ⟨2214426631058837856995833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2952568841411783809327777 2214426631058837856995833)
    ·
      refine ⟨1660819973294128392746875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2214426631058837856995833 1660819973294128392746875)
      ·
        refine ⟨2491229959941192589120313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1660819973294128392746875 2491229959941192589120313)
        ·
          refine ⟨1868422469955894441840235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2491229959941192589120313 1868422469955894441840235)
          ·
            refine ⟨2802633704933841662760353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1868422469955894441840235 2802633704933841662760353)
            ·
              refine ⟨2101975278700381247070265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2802633704933841662760353 2101975278700381247070265)
              ·
                refine ⟨1576481459025285935302699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2101975278700381247070265 1576481459025285935302699)
                ·
                  refine ⟨2364722188537928902954049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1576481459025285935302699 2364722188537928902954049)
                  ·
                    refine ⟨1773541641403446677215537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2364722188537928902954049 1773541641403446677215537)
                    ·
                      refine ⟨1330156231052585007911653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1773541641403446677215537 1330156231052585007911653)
                      ·
                        rfl

theorem cell23_2590470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_2590470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2590470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2590470 prefixEnd_2590470 := by exact prefixLift 2590470
  have htrace : WordTrace (prefixWord ++ tailWord_2590470) baseStart_2590470 baseEnd_2590470 := by
    simpa [prefixWord, tailWord_2590470, baseEnd_2590470] using wordTrace_append hprefix tailTrace_2590470
  have hstable : (prefixWord ++ tailWord_2590470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590470).length < 2 ^ (prefixWord ++ tailWord_2590470).sum := by decide
  have hdescent : baseEnd_2590470 < baseStart_2590470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590487 : List Nat := [1, 1, 3, 4, 2, 1, 2, 1, 1, 2, 5]
def baseStart_2590487 : Nat := 118140960795 + 2590487 * 2 ^ 59
def prefixEnd_2590487 : Nat := 4983230072969 + 3 ^ 40 * 2590487 * 2
def baseEnd_2590487 : Nat := 1330164960223711441399073

theorem tailTrace_2590487 : CollatzResearch.WordTrace tailWord_2590487 prefixEnd_2590487 1330164960223711441399073 := by
  unfold tailWord_2590487
  simp only [CollatzResearch.WordTrace]
  refine ⟨94482822966115493801857715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62988548644076995867905143 94482822966115493801857715)
  ·
    refine ⟨141724234449173240702786573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94482822966115493801857715 141724234449173240702786573)
    ·
      refine ⟨53146587918439965263544965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141724234449173240702786573 53146587918439965263544965)
      ·
        refine ⟨9964985234707493486914681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53146587918439965263544965 9964985234707493486914681)
        ·
          refine ⟨7473738926030620115186011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9964985234707493486914681 7473738926030620115186011)
          ·
            refine ⟨11210608389045930172779017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7473738926030620115186011 11210608389045930172779017)
            ·
              refine ⟨8407956291784447629584263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11210608389045930172779017 8407956291784447629584263)
              ·
                refine ⟨12611934437676671444376395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8407956291784447629584263 12611934437676671444376395)
                ·
                  refine ⟨18917901656515007166564593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12611934437676671444376395 18917901656515007166564593)
                  ·
                    refine ⟨14188426242386255374923445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18917901656515007166564593 14188426242386255374923445)
                    ·
                      refine ⟨1330164960223711441399073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14188426242386255374923445 1330164960223711441399073)
                      ·
                        rfl

theorem cell23_2590487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_2590487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2590487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2590487 prefixEnd_2590487 := by exact prefixLift 2590487
  have htrace : WordTrace (prefixWord ++ tailWord_2590487) baseStart_2590487 baseEnd_2590487 := by
    simpa [prefixWord, tailWord_2590487, baseEnd_2590487] using wordTrace_append hprefix tailTrace_2590487
  have hstable : (prefixWord ++ tailWord_2590487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590487).length < 2 ^ (prefixWord ++ tailWord_2590487).sum := by decide
  have hdescent : baseEnd_2590487 < baseStart_2590487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590514 : List Nat := [3, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4]
def baseStart_2590514 : Nat := 118140960795 + 2590514 * 2 ^ 59
def prefixEnd_2590514 : Nat := 4983230072969 + 3 ^ 40 * 2590514 * 2
def baseEnd_2590514 : Nat := 1330178824201382835761449

theorem tailTrace_2590514 : CollatzResearch.WordTrace tailWord_2590514 prefixEnd_2590514 1330178824201382835761449 := by
  unfold tailWord_2590514
  simp only [CollatzResearch.WordTrace]
  refine ⟨23620951934254419353272649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62989205158011784942060397 23620951934254419353272649)
  ·
    refine ⟨17715713950690814514954487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23620951934254419353272649 17715713950690814514954487)
    ·
      refine ⟨26573570926036221772431731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17715713950690814514954487 26573570926036221772431731)
      ·
        refine ⟨39860356389054332658647597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26573570926036221772431731 39860356389054332658647597)
        ·
          refine ⟨14947633645895374746992849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39860356389054332658647597 14947633645895374746992849)
          ·
            refine ⟨11210725234421531060244637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14947633645895374746992849 11210725234421531060244637)
            ·
              refine ⟨4204021962908074147591739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11210725234421531060244637 4204021962908074147591739)
              ·
                refine ⟨6306032944362111221387609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4204021962908074147591739 6306032944362111221387609)
                ·
                  refine ⟨4729524708271583416040707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6306032944362111221387609 4729524708271583416040707)
                  ·
                    refine ⟨7094287062407375124061061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4729524708271583416040707 7094287062407375124061061)
                    ·
                      refine ⟨1330178824201382835761449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7094287062407375124061061 1330178824201382835761449)
                      ·
                        rfl

theorem cell23_2590514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4].length) (baseStart_2590514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2590514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2590514 prefixEnd_2590514 := by exact prefixLift 2590514
  have htrace : WordTrace (prefixWord ++ tailWord_2590514) baseStart_2590514 baseEnd_2590514 := by
    simpa [prefixWord, tailWord_2590514, baseEnd_2590514] using wordTrace_append hprefix tailTrace_2590514
  have hstable : (prefixWord ++ tailWord_2590514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590514).length < 2 ^ (prefixWord ++ tailWord_2590514).sum := by decide
  have hdescent : baseEnd_2590514 < baseStart_2590514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590541 : List Nat := [1, 6, 1, 2, 1, 1, 1, 3, 3, 4]
def baseStart_2590541 : Nat := 118140960795 + 2590541 * 2 ^ 59
def prefixEnd_2590541 : Nat := 4983230072969 + 3 ^ 40 * 2590541 * 2
def baseEnd_2590541 : Nat := 443397562726351410041275

theorem tailTrace_2590541 : CollatzResearch.WordTrace tailWord_2590541 prefixEnd_2590541 443397562726351410041275 := by
  unfold tailWord_2590541
  simp only [CollatzResearch.WordTrace]
  refine ⟨94484792507919861024323477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62989861671946574016215651 94484792507919861024323477)
  ·
    refine ⟨4428974648808743485515163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 94484792507919861024323477 4428974648808743485515163)
    ·
      refine ⟨6643461973213115228272745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4428974648808743485515163 6643461973213115228272745)
      ·
        refine ⟨4982596479909836421204559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6643461973213115228272745 4982596479909836421204559)
        ·
          refine ⟨7473894719864754631806839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4982596479909836421204559 7473894719864754631806839)
          ·
            refine ⟨11210842079797131947710259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7473894719864754631806839 11210842079797131947710259)
            ·
              refine ⟨16816263119695697921565389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11210842079797131947710259 16816263119695697921565389)
              ·
                refine ⟨6306098669885886720587021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16816263119695697921565389 6306098669885886720587021)
                ·
                  refine ⟨2364787001207207520220133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6306098669885886720587021 2364787001207207520220133)
                  ·
                    refine ⟨443397562726351410041275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2364787001207207520220133 443397562726351410041275)
                    ·
                      rfl

theorem cell23_2590541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_2590541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2590541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2590541 prefixEnd_2590541 := by exact prefixLift 2590541
  have htrace : WordTrace (prefixWord ++ tailWord_2590541) baseStart_2590541 baseEnd_2590541 := by
    simpa [prefixWord, tailWord_2590541, baseEnd_2590541] using wordTrace_append hprefix tailTrace_2590541
  have hstable : (prefixWord ++ tailWord_2590541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590541).length < 2 ^ (prefixWord ++ tailWord_2590541).sum := by decide
  have hdescent : baseEnd_2590541 < baseStart_2590541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590554 : List Nat := [3, 1, 1, 2, 1, 3, 5, 1, 6]
def baseStart_2590554 : Nat := 118140960795 + 2590554 * 2 ^ 59
def prefixEnd_2590554 : Nat := 4983230072969 + 3 ^ 40 * 2590554 * 2
def baseEnd_2590554 : Nat := 147799929269729186584585

theorem tailTrace_2590554 : CollatzResearch.WordTrace tailWord_2590554 prefixEnd_2590554 147799929269729186584585 := by
  unfold tailWord_2590554
  simp only [CollatzResearch.WordTrace]
  refine ⟨23621316664218191061136679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62990177771248509496364477 23621316664218191061136679)
  ·
    refine ⟨35431974996327286591705019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23621316664218191061136679 35431974996327286591705019)
    ·
      refine ⟨53147962494490929887557529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35431974996327286591705019 53147962494490929887557529)
      ·
        refine ⟨39860971870868197415668147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53147962494490929887557529 39860971870868197415668147)
        ·
          refine ⟨59791457806302296123502221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39860971870868197415668147 59791457806302296123502221)
          ·
            refine ⟨22421796677363361046313333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59791457806302296123502221 22421796677363361046313333)
            ·
              refine ⟨2102043438502815098091875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22421796677363361046313333 2102043438502815098091875)
              ·
                refine ⟨3153065157754222647137813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2102043438502815098091875 3153065157754222647137813)
                ·
                  refine ⟨147799929269729186584585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3153065157754222647137813 147799929269729186584585)
                  ·
                    rfl

theorem cell23_2590554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 1, 6].length) (baseStart_2590554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2590554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2590554 prefixEnd_2590554 := by exact prefixLift 2590554
  have htrace : WordTrace (prefixWord ++ tailWord_2590554) baseStart_2590554 baseEnd_2590554 := by
    simpa [prefixWord, tailWord_2590554, baseEnd_2590554] using wordTrace_append hprefix tailTrace_2590554
  have hstable : (prefixWord ++ tailWord_2590554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590554).length < 2 ^ (prefixWord ++ tailWord_2590554).sum := by decide
  have hdescent : baseEnd_2590554 < baseStart_2590554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590587 : List Nat := [1, 1, 1, 1, 1, 5, 1, 2, 5, 1, 4]
def baseStart_2590587 : Nat := 118140960795 + 2590587 * 2 ^ 59
def prefixEnd_2590587 : Nat := 4983230072969 + 3 ^ 40 * 2590587 * 2
def baseEnd_2590587 : Nat := 1330216308289161050148613

theorem tailTrace_2590587 : CollatzResearch.WordTrace tailWord_2590587 prefixEnd_2590587 1330216308289161050148613 := by
  unfold tailWord_2590587
  simp only [CollatzResearch.WordTrace]
  refine ⟨94486470265753210880498015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62990980177168807253665343 94486470265753210880498015)
  ·
    refine ⟨141729705398629816320747023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94486470265753210880498015 141729705398629816320747023)
    ·
      refine ⟨212594558097944724481120535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141729705398629816320747023 212594558097944724481120535)
      ·
        refine ⟨318891837146917086721680803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212594558097944724481120535 318891837146917086721680803)
        ·
          refine ⟨478337755720375630082521205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318891837146917086721680803 478337755720375630082521205)
          ·
            refine ⟨44844164598785215320236363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 478337755720375630082521205 44844164598785215320236363)
            ·
              refine ⟨67266246898177822980354545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44844164598785215320236363 67266246898177822980354545)
              ·
                refine ⟨50449685173633367235265909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67266246898177822980354545 50449685173633367235265909)
                ·
                  refine ⟨4729657985028128178306179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50449685173633367235265909 4729657985028128178306179)
                  ·
                    refine ⟨7094486977542192267459269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4729657985028128178306179 7094486977542192267459269)
                    ·
                      refine ⟨1330216308289161050148613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7094486977542192267459269 1330216308289161050148613)
                      ·
                        rfl

theorem cell23_2590587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 5, 1, 4].length) (baseStart_2590587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2590587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2590587 prefixEnd_2590587 := by exact prefixLift 2590587
  have htrace : WordTrace (prefixWord ++ tailWord_2590587) baseStart_2590587 baseEnd_2590587 := by
    simpa [prefixWord, tailWord_2590587, baseEnd_2590587] using wordTrace_append hprefix tailTrace_2590587
  have hstable : (prefixWord ++ tailWord_2590587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590587).length < 2 ^ (prefixWord ++ tailWord_2590587).sum := by decide
  have hdescent : baseEnd_2590587 < baseStart_2590587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590617 : List Nat := [1, 2, 1, 2, 1, 3, 4, 1, 1, 1, 6]
def baseStart_2590617 : Nat := 118140960795 + 2590617 * 2 ^ 59
def prefixEnd_2590617 : Nat := 4983230072969 + 3 ^ 40 * 2590617 * 2
def baseEnd_2590617 : Nat := 1330231712708795932773475

theorem tailTrace_2590617 : CollatzResearch.WordTrace tailWord_2590617 prefixEnd_2590617 1330231712708795932773475 := by
  unfold tailWord_2590617
  simp only [CollatzResearch.WordTrace]
  refine ⟨94487564455644526004090105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62991709637096350669393403 94487564455644526004090105)
  ·
    refine ⟨70865673341733394503067579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94487564455644526004090105 70865673341733394503067579)
    ·
      refine ⟨106298510012600091754601369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70865673341733394503067579 106298510012600091754601369)
      ·
        refine ⟨79723882509450068815951027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106298510012600091754601369 79723882509450068815951027)
        ·
          refine ⟨119585823764175103223926541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79723882509450068815951027 119585823764175103223926541)
          ·
            refine ⟨44844683911565663708972453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119585823764175103223926541 44844683911565663708972453)
            ·
              refine ⟨8408378233418561945432335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44844683911565663708972453 8408378233418561945432335)
              ·
                refine ⟨12612567350127842918148503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8408378233418561945432335 12612567350127842918148503)
                ·
                  refine ⟨18918851025191764377222755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12612567350127842918148503 18918851025191764377222755)
                  ·
                    refine ⟨28378276537787646565834133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18918851025191764377222755 28378276537787646565834133)
                    ·
                      refine ⟨1330231712708795932773475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28378276537787646565834133 1330231712708795932773475)
                      ·
                        rfl

theorem cell23_2590617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 1, 6].length) (baseStart_2590617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2590617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2590617 prefixEnd_2590617 := by exact prefixLift 2590617
  have htrace : WordTrace (prefixWord ++ tailWord_2590617) baseStart_2590617 baseEnd_2590617 := by
    simpa [prefixWord, tailWord_2590617, baseEnd_2590617] using wordTrace_append hprefix tailTrace_2590617
  have hstable : (prefixWord ++ tailWord_2590617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590617).length < 2 ^ (prefixWord ++ tailWord_2590617).sum := by decide
  have hdescent : baseEnd_2590617 < baseStart_2590617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590621 : List Nat := [1, 4, 2, 1, 2, 2, 3, 2, 1, 1, 4]
def baseStart_2590621 : Nat := 118140960795 + 2590621 * 2 ^ 59
def prefixEnd_2590621 : Nat := 4983230072969 + 3 ^ 40 * 2590621 * 2
def baseEnd_2590621 : Nat := 1330233766631413917123457

theorem tailTrace_2590621 : CollatzResearch.WordTrace tailWord_2590621 prefixEnd_2590621 1330233766631413917123457 := by
  unfold tailWord_2590621
  simp only [CollatzResearch.WordTrace]
  refine ⟨94487710347630034687235717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62991806898420023124823811 94487710347630034687235717)
  ·
    refine ⟨17716445690180631503856697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94487710347630034687235717 17716445690180631503856697)
    ·
      refine ⟨13287334267635473627892523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17716445690180631503856697 13287334267635473627892523)
      ·
        refine ⟨19931001401453210441838785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13287334267635473627892523 19931001401453210441838785)
        ·
          refine ⟨14948251051089907831379089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19931001401453210441838785 14948251051089907831379089)
          ·
            refine ⟨11211188288317430873534317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14948251051089907831379089 11211188288317430873534317)
            ·
              refine ⟨4204195608119036577575369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11211188288317430873534317 4204195608119036577575369)
              ·
                refine ⟨3153146706089277433181527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4204195608119036577575369 3153146706089277433181527)
                ·
                  refine ⟨4729720059133916149772291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3153146706089277433181527 4729720059133916149772291)
                  ·
                    refine ⟨7094580088700874224658437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4729720059133916149772291 7094580088700874224658437)
                    ·
                      refine ⟨1330233766631413917123457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7094580088700874224658437 1330233766631413917123457)
                      ·
                        rfl

theorem cell23_2590621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_2590621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2590621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2590621 prefixEnd_2590621 := by exact prefixLift 2590621
  have htrace : WordTrace (prefixWord ++ tailWord_2590621) baseStart_2590621 baseEnd_2590621 := by
    simpa [prefixWord, tailWord_2590621, baseEnd_2590621] using wordTrace_append hprefix tailTrace_2590621
  have hstable : (prefixWord ++ tailWord_2590621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590621).length < 2 ^ (prefixWord ++ tailWord_2590621).sum := by decide
  have hdescent : baseEnd_2590621 < baseStart_2590621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590641 : List Nat := [1, 2, 2, 4, 2, 3, 1, 1, 1, 1, 5]
def baseStart_2590641 : Nat := 118140960795 + 2590641 * 2 ^ 59
def prefixEnd_2590641 : Nat := 4983230072969 + 3 ^ 40 * 2590641 * 2
def baseEnd_2590641 : Nat := 1330244036244503838873365

theorem tailTrace_2590641 : CollatzResearch.WordTrace tailWord_2590641 prefixEnd_2590641 1330244036244503838873365 := by
  unfold tailWord_2590641
  simp only [CollatzResearch.WordTrace]
  refine ⟨94488439807557578102963777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62992293205038385401975851 94488439807557578102963777)
  ·
    refine ⟨70866329855668183577222833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94488439807557578102963777 70866329855668183577222833)
    ·
      refine ⟨53149747391751137682917125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70866329855668183577222833 53149747391751137682917125)
      ·
        refine ⟨9965577635953338315546961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53149747391751137682917125 9965577635953338315546961)
        ·
          refine ⟨7474183226965003736660221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9965577635953338315546961 7474183226965003736660221)
          ·
            refine ⟨2802818710111876401247583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7474183226965003736660221 2802818710111876401247583)
            ·
              refine ⟨4204228065167814601871375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2802818710111876401247583 4204228065167814601871375)
              ·
                refine ⟨6306342097751721902807063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4204228065167814601871375 6306342097751721902807063)
                ·
                  refine ⟨9459513146627582854210595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6306342097751721902807063 9459513146627582854210595)
                  ·
                    refine ⟨14189269719941374281315893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9459513146627582854210595 14189269719941374281315893)
                    ·
                      refine ⟨1330244036244503838873365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14189269719941374281315893 1330244036244503838873365)
                      ·
                        rfl

theorem cell23_2590641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_2590641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2590641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2590641 prefixEnd_2590641 := by exact prefixLift 2590641
  have htrace : WordTrace (prefixWord ++ tailWord_2590641) baseStart_2590641 baseEnd_2590641 := by
    simpa [prefixWord, tailWord_2590641, baseEnd_2590641] using wordTrace_append hprefix tailTrace_2590641
  have hstable : (prefixWord ++ tailWord_2590641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590641).length < 2 ^ (prefixWord ++ tailWord_2590641).sum := by decide
  have hdescent : baseEnd_2590641 < baseStart_2590641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590644 : List Nat := [2, 5, 2, 1, 13]
def baseStart_2590644 : Nat := 118140960795 + 2590644 * 2 ^ 59
def prefixEnd_2590644 : Nat := 4983230072969 + 3 ^ 40 * 2590644 * 2
def baseEnd_2590644 : Nat := 1824753877484866018019

theorem tailTrace_2590644 : CollatzResearch.WordTrace tailWord_2590644 prefixEnd_2590644 1824753877484866018019 := by
  unfold tailWord_2590644
  simp only [CollatzResearch.WordTrace]
  refine ⟨47244274613273354807661493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62992366151031139743548657 47244274613273354807661493)
  ·
    refine ⟨4429150744994377013218265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47244274613273354807661493 4429150744994377013218265)
    ·
      refine ⟨3321863058745782759913699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4429150744994377013218265 3321863058745782759913699)
      ·
        refine ⟨4982794588118674139870549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3321863058745782759913699 4982794588118674139870549)
        ·
          refine ⟨1824753877484866018019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 4982794588118674139870549 1824753877484866018019)
          ·
            rfl

theorem cell23_2590644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 13].length) (baseStart_2590644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2590644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2590644 prefixEnd_2590644 := by exact prefixLift 2590644
  have htrace : WordTrace (prefixWord ++ tailWord_2590644) baseStart_2590644 baseEnd_2590644 := by
    simpa [prefixWord, tailWord_2590644, baseEnd_2590644] using wordTrace_append hprefix tailTrace_2590644
  have hstable : (prefixWord ++ tailWord_2590644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590644).length < 2 ^ (prefixWord ++ tailWord_2590644).sum := by decide
  have hdescent : baseEnd_2590644 < baseStart_2590644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590671 : List Nat := [1, 1, 2, 1, 1, 5, 1, 5, 2, 1, 3]
def baseStart_2590671 : Nat := 118140960795 + 2590671 * 2 ^ 59
def prefixEnd_2590671 : Nat := 4983230072969 + 3 ^ 40 * 2590671 * 2
def baseEnd_2590671 : Nat := 1330259440664138721498227

theorem tailTrace_2590671 : CollatzResearch.WordTrace tailWord_2590671 prefixEnd_2590671 1330259440664138721498227 := by
  unfold tailWord_2590671
  simp only [CollatzResearch.WordTrace]
  refine ⟨94489533997448893226555867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62993022664965928817703911 94489533997448893226555867)
  ·
    refine ⟨141734300996173339839833801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94489533997448893226555867 141734300996173339839833801)
    ·
      refine ⟨106300725747130004879875351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141734300996173339839833801 106300725747130004879875351)
      ·
        refine ⟨159451088620695007319813027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106300725747130004879875351 159451088620695007319813027)
        ·
          refine ⟨239176632931042510979719541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159451088620695007319813027 239176632931042510979719541)
          ·
            refine ⟨22422809337285235404348707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 239176632931042510979719541 22422809337285235404348707)
            ·
              refine ⟨33634214005927853106523061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22422809337285235404348707 33634214005927853106523061)
              ·
                refine ⟨3153207563055736228736537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33634214005927853106523061 3153207563055736228736537)
                ·
                  refine ⟨2364905672291802171552403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3153207563055736228736537 2364905672291802171552403)
                  ·
                    refine ⟨3547358508437703257328605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2364905672291802171552403 3547358508437703257328605)
                    ·
                      refine ⟨1330259440664138721498227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3547358508437703257328605 1330259440664138721498227)
                      ·
                        rfl

theorem cell23_2590671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 5, 2, 1, 3].length) (baseStart_2590671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2590671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2590671 prefixEnd_2590671 := by exact prefixLift 2590671
  have htrace : WordTrace (prefixWord ++ tailWord_2590671) baseStart_2590671 baseEnd_2590671 := by
    simpa [prefixWord, tailWord_2590671, baseEnd_2590671] using wordTrace_append hprefix tailTrace_2590671
  have hstable : (prefixWord ++ tailWord_2590671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590671).length < 2 ^ (prefixWord ++ tailWord_2590671).sum := by decide
  have hdescent : baseEnd_2590671 < baseStart_2590671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590678 : List Nat := [5, 2, 1, 1, 3, 1, 3, 7]
def baseStart_2590678 : Nat := 118140960795 + 2590678 * 2 ^ 59
def prefixEnd_2590678 : Nat := 4983230072969 + 3 ^ 40 * 2590678 * 2
def baseEnd_2590678 : Nat := 49269001297360007189285

theorem tailTrace_2590678 : CollatzResearch.WordTrace tailWord_2590678 prefixEnd_2590678 49269001297360007189285 := by
  unfold tailWord_2590678
  simp only [CollatzResearch.WordTrace]
  refine ⟨5905611831776470838878793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62993192872282355614707125 5905611831776470838878793)
  ·
    refine ⟨4429208873832353129159095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5905611831776470838878793 4429208873832353129159095)
    ·
      refine ⟨6643813310748529693738643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4429208873832353129159095 6643813310748529693738643)
      ·
        refine ⟨9965719966122794540607965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6643813310748529693738643 9965719966122794540607965)
        ·
          refine ⟨3737144987296047952727987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9965719966122794540607965 3737144987296047952727987)
          ·
            refine ⟨5605717480944071929091981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3737144987296047952727987 5605717480944071929091981)
            ·
              refine ⟨2102144055354026973409493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5605717480944071929091981 2102144055354026973409493)
              ·
                refine ⟨49269001297360007189285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2102144055354026973409493 49269001297360007189285)
                ·
                  rfl

theorem cell23_2590678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 7].length) (baseStart_2590678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2590678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2590678 prefixEnd_2590678 := by exact prefixLift 2590678
  have htrace : WordTrace (prefixWord ++ tailWord_2590678) baseStart_2590678 baseEnd_2590678 := by
    simpa [prefixWord, tailWord_2590678, baseEnd_2590678] using wordTrace_append hprefix tailTrace_2590678
  have hstable : (prefixWord ++ tailWord_2590678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590678).length < 2 ^ (prefixWord ++ tailWord_2590678).sum := by decide
  have hdescent : baseEnd_2590678 < baseStart_2590678 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590698 : List Nat := [3, 1, 3, 1, 2, 1, 3, 3, 1, 3, 2]
def baseStart_2590698 : Nat := 118140960795 + 2590698 * 2 ^ 59
def prefixEnd_2590698 : Nat := 4983230072969 + 3 ^ 40 * 2590698 * 2
def baseEnd_2590698 : Nat := 1330273304641810115860603

theorem tailTrace_2590698 : CollatzResearch.WordTrace tailWord_2590698 prefixEnd_2590698 1330273304641810115860603 := by
  unfold tailWord_2590698
  simp only [CollatzResearch.WordTrace]
  refine ⟨23622629692087769209447187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62993679178900717891859165 23622629692087769209447187)
  ·
    refine ⟨35433944538131653814170781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23622629692087769209447187 35433944538131653814170781)
    ·
      refine ⟨13287729201799370180314043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35433944538131653814170781 13287729201799370180314043)
      ·
        refine ⟨19931593802699055270471065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13287729201799370180314043 19931593802699055270471065)
        ·
          refine ⟨14948695352024291452853299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19931593802699055270471065 14948695352024291452853299)
          ·
            refine ⟨22423043028036437179279949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14948695352024291452853299 22423043028036437179279949)
            ·
              refine ⟨8408641135513663942229981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22423043028036437179279949 8408641135513663942229981)
              ·
                refine ⟨3153240425817623978336243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8408641135513663942229981 3153240425817623978336243)
                ·
                  refine ⟨4729860638726435967504365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3153240425817623978336243 4729860638726435967504365)
                  ·
                    refine ⟨1773697739522413487814137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4729860638726435967504365 1773697739522413487814137)
                    ·
                      refine ⟨1330273304641810115860603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1773697739522413487814137 1330273304641810115860603)
                      ·
                        rfl

theorem cell23_2590698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 3, 1, 3, 2].length) (baseStart_2590698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2590698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2590698 prefixEnd_2590698 := by exact prefixLift 2590698
  have htrace : WordTrace (prefixWord ++ tailWord_2590698) baseStart_2590698 baseEnd_2590698 := by
    simpa [prefixWord, tailWord_2590698, baseEnd_2590698] using wordTrace_append hprefix tailTrace_2590698
  have hstable : (prefixWord ++ tailWord_2590698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590698).length < 2 ^ (prefixWord ++ tailWord_2590698).sum := by decide
  have hdescent : baseEnd_2590698 < baseStart_2590698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590705 : List Nat := [1, 2, 2, 2, 5, 2, 1, 2, 2, 1, 3]
def baseStart_2590705 : Nat := 118140960795 + 2590705 * 2 ^ 59
def prefixEnd_2590705 : Nat := 4983230072969 + 3 ^ 40 * 2590705 * 2
def baseEnd_2590705 : Nat := 1330276899006391588473071

theorem tailTrace_2590705 : CollatzResearch.WordTrace tailWord_2590705 prefixEnd_2590705 1330276899006391588473071 := by
  unfold tailWord_2590705
  simp only [CollatzResearch.WordTrace]
  refine ⟨94490774079325717033293569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62993849386217144688862379 94490774079325717033293569)
  ·
    refine ⟨70868080559494287774970177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94490774079325717033293569 70868080559494287774970177)
    ·
      refine ⟨53151060419620715831227633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70868080559494287774970177 53151060419620715831227633)
      ·
        refine ⟨39863295314715536873420725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53151060419620715831227633 39863295314715536873420725)
        ·
          refine ⟨3737183935754581581883193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39863295314715536873420725 3737183935754581581883193)
          ·
            refine ⟨2802887951815936186412395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3737183935754581581883193 2802887951815936186412395)
            ·
              refine ⟨4204331927723904279618593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2802887951815936186412395 4204331927723904279618593)
              ·
                refine ⟨3153248945792928209713945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4204331927723904279618593 3153248945792928209713945)
                ·
                  refine ⟨2364936709344696157285459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3153248945792928209713945 2364936709344696157285459)
                  ·
                    refine ⟨3547405064017044235928189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2364936709344696157285459 3547405064017044235928189)
                    ·
                      refine ⟨1330276899006391588473071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3547405064017044235928189 1330276899006391588473071)
                      ·
                        rfl

theorem cell23_2590705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 2, 2, 1, 3].length) (baseStart_2590705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2590705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2590705 prefixEnd_2590705 := by exact prefixLift 2590705
  have htrace : WordTrace (prefixWord ++ tailWord_2590705) baseStart_2590705 baseEnd_2590705 := by
    simpa [prefixWord, tailWord_2590705, baseEnd_2590705] using wordTrace_append hprefix tailTrace_2590705
  have hstable : (prefixWord ++ tailWord_2590705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590705).length < 2 ^ (prefixWord ++ tailWord_2590705).sum := by decide
  have hdescent : baseEnd_2590705 < baseStart_2590705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590734 : List Nat := [4, 1, 1, 2, 2, 1, 1, 4, 7]
def baseStart_2590734 : Nat := 118140960795 + 2590734 * 2 ^ 59
def prefixEnd_2590734 : Nat := 4983230072969 + 3 ^ 40 * 2590734 * 2
def baseEnd_2590734 : Nat := 147810198882819108334493

theorem tailTrace_2590734 : CollatzResearch.WordTrace tailWord_2590734 prefixEnd_2590734 147810198882819108334493 := by
  unfold tailWord_2590734
  simp only [CollatzResearch.WordTrace]
  refine ⟨11811478974527581873262407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62994554530813769990732837 11811478974527581873262407)
  ·
    refine ⟨17717218461791372809893611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11811478974527581873262407 17717218461791372809893611)
    ·
      refine ⟨26575827692687059214840417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17717218461791372809893611 26575827692687059214840417)
      ·
        refine ⟨19931870769515294411130313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26575827692687059214840417 19931870769515294411130313)
        ·
          refine ⟨14948903077136470808347735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19931870769515294411130313 14948903077136470808347735)
          ·
            refine ⟨22423354615704706212521603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14948903077136470808347735 22423354615704706212521603)
            ·
              refine ⟨33635031923557059318782405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22423354615704706212521603 33635031923557059318782405)
              ·
                refine ⟨6306568485666948622271701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33635031923557059318782405 6306568485666948622271701)
                ·
                  refine ⟨147810198882819108334493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6306568485666948622271701 147810198882819108334493)
                  ·
                    rfl

theorem cell23_2590734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4, 7].length) (baseStart_2590734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2590734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2590734 prefixEnd_2590734 := by exact prefixLift 2590734
  have htrace : WordTrace (prefixWord ++ tailWord_2590734) baseStart_2590734 baseEnd_2590734 := by
    simpa [prefixWord, tailWord_2590734, baseEnd_2590734] using wordTrace_append hprefix tailTrace_2590734
  have hstable : (prefixWord ++ tailWord_2590734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590734).length < 2 ^ (prefixWord ++ tailWord_2590734).sum := by decide
  have hdescent : baseEnd_2590734 < baseStart_2590734 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590768 : List Nat := [2, 1, 1, 1, 2, 6, 3, 2, 5]
def baseStart_2590768 : Nat := 118140960795 + 2590768 * 2 ^ 59
def prefixEnd_2590768 : Nat := 4983230072969 + 3 ^ 40 * 2590768 * 2
def baseEnd_2590768 : Nat := 147812138698624982442809

theorem tailTrace_2590768 : CollatzResearch.WordTrace tailWord_2590768 prefixEnd_2590768 147812138698624982442809 := by
  unfold tailWord_2590768
  simp only [CollatzResearch.WordTrace]
  refine ⟨47246535939048739396418479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62995381252064985861891305 47246535939048739396418479)
  ·
    refine ⟨70869803908573109094627719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47246535939048739396418479 70869803908573109094627719)
    ·
      refine ⟨106304705862859663641941579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70869803908573109094627719 106304705862859663641941579)
      ·
        refine ⟨159457058794289495462912369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106304705862859663641941579 159457058794289495462912369)
        ·
          refine ⟨119592794095717121597184277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159457058794289495462912369 119592794095717121597184277)
          ·
            refine ⟨5605912223236740074868013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 119592794095717121597184277 5605912223236740074868013)
            ·
              refine ⟨2102217083713777528075505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5605912223236740074868013 2102217083713777528075505)
              ·
                refine ⟨1576662812785333146056629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2102217083713777528075505 1576662812785333146056629)
                ·
                  refine ⟨147812138698624982442809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1576662812785333146056629 147812138698624982442809)
                  ·
                    rfl

theorem cell23_2590768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 2, 5].length) (baseStart_2590768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2590768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2590768 prefixEnd_2590768 := by exact prefixLift 2590768
  have htrace : WordTrace (prefixWord ++ tailWord_2590768) baseStart_2590768 baseEnd_2590768 := by
    simpa [prefixWord, tailWord_2590768, baseEnd_2590768] using wordTrace_append hprefix tailTrace_2590768
  have hstable : (prefixWord ++ tailWord_2590768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590768).length < 2 ^ (prefixWord ++ tailWord_2590768).sum := by decide
  have hdescent : baseEnd_2590768 < baseStart_2590768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590801 : List Nat := [1, 2, 2, 1, 3, 1, 1, 2, 4, 4, 2]
def baseStart_2590801 : Nat := 118140960795 + 2590801 * 2 ^ 59
def prefixEnd_2590801 : Nat := 4983230072969 + 3 ^ 40 * 2590801 * 2
def baseEnd_2590801 : Nat := 1330326193149223212872629

theorem tailTrace_2590801 : CollatzResearch.WordTrace tailWord_2590801 prefixEnd_2590801 1330326193149223212872629 := by
  unfold tailWord_2590801
  simp only [CollatzResearch.WordTrace]
  refine ⟨94494275486977925428788257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62996183657985283619192171 94494275486977925428788257)
  ·
    refine ⟨70870706615233444071591193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94494275486977925428788257 70870706615233444071591193)
    ·
      refine ⟨53153029961425083053693395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70870706615233444071591193 53153029961425083053693395)
      ·
        refine ⟨79729544942137624580540093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53153029961425083053693395 79729544942137624580540093)
        ·
          refine ⟨29898579353301609217702535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79729544942137624580540093 29898579353301609217702535)
          ·
            refine ⟨44847869029952413826553803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29898579353301609217702535 44847869029952413826553803)
            ·
              refine ⟨67271803544928620739830705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44847869029952413826553803 67271803544928620739830705)
              ·
                refine ⟨50453852658696465554873029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67271803544928620739830705 50453852658696465554873029)
                ·
                  refine ⟨9460097373505587291538693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50453852658696465554873029 9460097373505587291538693)
                  ·
                    refine ⟨1773768257532297617163505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9460097373505587291538693 1773768257532297617163505)
                    ·
                      refine ⟨1330326193149223212872629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1773768257532297617163505 1330326193149223212872629)
                      ·
                        rfl

theorem cell23_2590801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4, 4, 2].length) (baseStart_2590801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2590801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2590801 prefixEnd_2590801 := by exact prefixLift 2590801
  have htrace : WordTrace (prefixWord ++ tailWord_2590801) baseStart_2590801 baseEnd_2590801 := by
    simpa [prefixWord, tailWord_2590801, baseEnd_2590801] using wordTrace_append hprefix tailTrace_2590801
  have hstable : (prefixWord ++ tailWord_2590801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590801).length < 2 ^ (prefixWord ++ tailWord_2590801).sum := by decide
  have hdescent : baseEnd_2590801 < baseStart_2590801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590841 : List Nat := [1, 2, 1, 3, 4, 1, 2, 3, 6]
def baseStart_2590841 : Nat := 118140960795 + 2590841 * 2 ^ 59
def prefixEnd_2590841 : Nat := 4983230072969 + 3 ^ 40 * 2590841 * 2
def baseEnd_2590841 : Nat := 147816303597267006263605

theorem tailTrace_2590841 : CollatzResearch.WordTrace tailWord_2590841 prefixEnd_2590841 147816303597267006263605 := by
  unfold tailWord_2590841
  simp only [CollatzResearch.WordTrace]
  refine ⟨94495734406833012260244377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62997156271222008173496251 94495734406833012260244377)
  ·
    refine ⟨70871800805124759195183283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94495734406833012260244377 70871800805124759195183283)
    ·
      refine ⟨106307701207687138792774925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70871800805124759195183283 106307701207687138792774925)
      ·
        refine ⟨39865387952882677047290597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106307701207687138792774925 39865387952882677047290597)
        ·
          refine ⟨7474760241165501946366987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39865387952882677047290597 7474760241165501946366987)
          ·
            refine ⟨11212140361748252919550481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7474760241165501946366987 11212140361748252919550481)
            ·
              refine ⟨8409105271311189689662861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11212140361748252919550481 8409105271311189689662861)
              ·
                refine ⟨3153414476741696133623573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8409105271311189689662861 3153414476741696133623573)
                ·
                  refine ⟨147816303597267006263605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3153414476741696133623573 147816303597267006263605)
                  ·
                    rfl

theorem cell23_2590841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 3, 6].length) (baseStart_2590841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2590841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2590841 prefixEnd_2590841 := by exact prefixLift 2590841
  have htrace : WordTrace (prefixWord ++ tailWord_2590841) baseStart_2590841 baseEnd_2590841 := by
    simpa [prefixWord, tailWord_2590841, baseEnd_2590841] using wordTrace_append hprefix tailTrace_2590841
  have hstable : (prefixWord ++ tailWord_2590841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590841).length < 2 ^ (prefixWord ++ tailWord_2590841).sum := by decide
  have hdescent : baseEnd_2590841 < baseStart_2590841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590862 : List Nat := [4, 1, 1, 3, 3, 1, 2, 3, 1, 4]
def baseStart_2590862 : Nat := 118140960795 + 2590862 * 2 ^ 59
def prefixEnd_2590862 : Nat := 4983230072969 + 3 ^ 40 * 2590862 * 2
def baseEnd_2590862 : Nat := 443452505156382491403283

theorem tailTrace_2590862 : CollatzResearch.WordTrace tailWord_2590862 prefixEnd_2590862 443452505156382491403283 := by
  unfold tailWord_2590862
  simp only [CollatzResearch.WordTrace]
  refine ⟨11812062542469616605844855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62997666893171288564505893 11812062542469616605844855)
  ·
    refine ⟨17718093813704424908767283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11812062542469616605844855 17718093813704424908767283)
    ·
      refine ⟨26577140720556637363150925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17718093813704424908767283 26577140720556637363150925)
      ·
        refine ⟨9966427770208739011181597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26577140720556637363150925 9966427770208739011181597)
        ·
          refine ⟨3737410413828277129193099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9966427770208739011181597 3737410413828277129193099)
          ·
            refine ⟨5606115620742415693789649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3737410413828277129193099 5606115620742415693789649)
            ·
              refine ⟨4204586715556811770342237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5606115620742415693789649 4204586715556811770342237)
              ·
                refine ⟨1576720018333804413878339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4204586715556811770342237 1576720018333804413878339)
                ·
                  refine ⟨2365080027500706620817509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1576720018333804413878339 2365080027500706620817509)
                  ·
                    refine ⟨443452505156382491403283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2365080027500706620817509 443452505156382491403283)
                    ·
                      rfl

theorem cell23_2590862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 3, 1, 4].length) (baseStart_2590862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2590862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2590862 prefixEnd_2590862 := by exact prefixLift 2590862
  have htrace : WordTrace (prefixWord ++ tailWord_2590862) baseStart_2590862 baseEnd_2590862 := by
    simpa [prefixWord, tailWord_2590862, baseEnd_2590862] using wordTrace_append hprefix tailTrace_2590862
  have hstable : (prefixWord ++ tailWord_2590862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590862).length < 2 ^ (prefixWord ++ tailWord_2590862).sum := by decide
  have hdescent : baseEnd_2590862 < baseStart_2590862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590885 : List Nat := [1, 3, 1, 2, 1, 3, 1, 6, 1, 1, 3]
def baseStart_2590885 : Nat := 118140960795 + 2590885 * 2 ^ 59
def prefixEnd_2590885 : Nat := 4983230072969 + 3 ^ 40 * 2590885 * 2
def baseEnd_2590885 : Nat := 1330369325524200884222243

theorem tailTrace_2590885 : CollatzResearch.WordTrace tailWord_2590885 prefixEnd_2590885 1330369325524200884222243 := by
  unfold tailWord_2590885
  simp only [CollatzResearch.WordTrace]
  refine ⟨94497339218673607774846109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62998226145782405183230739 94497339218673607774846109)
  ·
    refine ⟨35436502207002602915567291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94497339218673607774846109 35436502207002602915567291)
    ·
      refine ⟨53154753310503904373350937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35436502207002602915567291 53154753310503904373350937)
      ·
        refine ⟨39866064982877928280013203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53154753310503904373350937 39866064982877928280013203)
        ·
          refine ⟨59799097474316892420019805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39866064982877928280013203 59799097474316892420019805)
          ·
            refine ⟨22424661552868834657507427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59799097474316892420019805 22424661552868834657507427)
            ·
              refine ⟨33636992329303251986261141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22424661552868834657507427 33636992329303251986261141)
              ·
                refine ⟨1576734015436089936855991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33636992329303251986261141 1576734015436089936855991)
                ·
                  refine ⟨2365101023154134905283987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1576734015436089936855991 2365101023154134905283987)
                  ·
                    refine ⟨3547651534731202357925981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2365101023154134905283987 3547651534731202357925981)
                    ·
                      refine ⟨1330369325524200884222243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3547651534731202357925981 1330369325524200884222243)
                      ·
                        rfl

theorem cell23_2590885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 6, 1, 1, 3].length) (baseStart_2590885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2590885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2590885 prefixEnd_2590885 := by exact prefixLift 2590885
  have htrace : WordTrace (prefixWord ++ tailWord_2590885) baseStart_2590885 baseEnd_2590885 := by
    simpa [prefixWord, tailWord_2590885, baseEnd_2590885] using wordTrace_append hprefix tailTrace_2590885
  have hstable : (prefixWord ++ tailWord_2590885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590885).length < 2 ^ (prefixWord ++ tailWord_2590885).sum := by decide
  have hdescent : baseEnd_2590885 < baseStart_2590885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590952 : List Nat := [2, 1, 4, 1, 2, 4, 2, 1, 2, 4]
def baseStart_2590952 : Nat := 118140960795 + 2590952 * 2 ^ 59
def prefixEnd_2590952 : Nat := 4983230072969 + 3 ^ 40 * 2590952 * 2
def baseEnd_2590952 : Nat := 443467909576017374028145

theorem tailTrace_2590952 : CollatzResearch.WordTrace tailWord_2590952 prefixEnd_2590952 443467909576017374028145 := by
  unfold tailWord_2590952
  simp only [CollatzResearch.WordTrace]
  refine ⟨47249891454715439108767555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62999855272953918811690073 47249891454715439108767555)
  ·
    refine ⟨70874837182073158663151333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47249891454715439108767555 70874837182073158663151333)
    ·
      refine ⟨13289031971638717249340875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70874837182073158663151333 13289031971638717249340875)
      ·
        refine ⟨19933547957458075874011313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13289031971638717249340875 19933547957458075874011313)
        ·
          refine ⟨14950160968093556905508485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19933547957458075874011313 14950160968093556905508485)
          ·
            refine ⟨2803155181517541919782841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14950160968093556905508485 2803155181517541919782841)
            ·
              refine ⟨2102366386138156439837131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2803155181517541919782841 2102366386138156439837131)
              ·
                refine ⟨3153549579207234659755697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2102366386138156439837131 3153549579207234659755697)
                ·
                  refine ⟨2365162184405425994816773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3153549579207234659755697 2365162184405425994816773)
                  ·
                    refine ⟨443467909576017374028145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2365162184405425994816773 443467909576017374028145)
                    ·
                      rfl

theorem cell23_2590952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 1, 2, 4].length) (baseStart_2590952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2590952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2590952 prefixEnd_2590952 := by exact prefixLift 2590952
  have htrace : WordTrace (prefixWord ++ tailWord_2590952) baseStart_2590952 baseEnd_2590952 := by
    simpa [prefixWord, tailWord_2590952, baseEnd_2590952] using wordTrace_append hprefix tailTrace_2590952
  have hstable : (prefixWord ++ tailWord_2590952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590952).length < 2 ^ (prefixWord ++ tailWord_2590952).sum := by decide
  have hdescent : baseEnd_2590952 < baseStart_2590952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590958 : List Nat := [4, 1, 2, 1, 1, 1, 1, 5, 1, 3, 3]
def baseStart_2590958 : Nat := 118140960795 + 2590958 * 2 ^ 59
def prefixEnd_2590958 : Nat := 4983230072969 + 3 ^ 40 * 2590958 * 2
def baseEnd_2590958 : Nat := 1330406809611979098609407

theorem tailTrace_2590958 : CollatzResearch.WordTrace tailWord_2590958 prefixEnd_2590958 1330406809611979098609407 := by
  unfold tailWord_2590958
  simp only [CollatzResearch.WordTrace]
  refine ⟨11812500218426142655281691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63000001164939427494835685 11812500218426142655281691)
  ·
    refine ⟨17718750327639213982922537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11812500218426142655281691 17718750327639213982922537)
    ·
      refine ⟨13289062745729410487191903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17718750327639213982922537 13289062745729410487191903)
      ·
        refine ⟨19933594118594115730787855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13289062745729410487191903 19933594118594115730787855)
        ·
          refine ⟨29900391177891173596181783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19933594118594115730787855 29900391177891173596181783)
          ·
            refine ⟨44850586766836760394272675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29900391177891173596181783 44850586766836760394272675)
            ·
              refine ⟨67275880150255140591409013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44850586766836760394272675 67275880150255140591409013)
              ·
                refine ⟨6307113764086419430444595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67275880150255140591409013 6307113764086419430444595)
                ·
                  refine ⟨9460670646129629145666893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6307113764086419430444595 9460670646129629145666893)
                  ·
                    refine ⟨3547751492298610929625085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9460670646129629145666893 3547751492298610929625085)
                    ·
                      refine ⟨1330406809611979098609407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3547751492298610929625085 1330406809611979098609407)
                      ·
                        rfl

theorem cell23_2590958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_2590958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2590958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2590958 prefixEnd_2590958 := by exact prefixLift 2590958
  have htrace : WordTrace (prefixWord ++ tailWord_2590958) baseStart_2590958 baseEnd_2590958 := by
    simpa [prefixWord, tailWord_2590958, baseEnd_2590958] using wordTrace_append hprefix tailTrace_2590958
  have hstable : (prefixWord ++ tailWord_2590958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590958).length < 2 ^ (prefixWord ++ tailWord_2590958).sum := by decide
  have hdescent : baseEnd_2590958 < baseStart_2590958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2590962 : List Nat := [3, 2, 1, 3, 2, 3, 1, 2, 1, 2, 3]
def baseStart_2590962 : Nat := 118140960795 + 2590962 * 2 ^ 59
def prefixEnd_2590962 : Nat := 4983230072969 + 3 ^ 40 * 2590962 * 2
def baseEnd_2590962 : Nat := 1330408863534597082959389

theorem tailTrace_2590962 : CollatzResearch.WordTrace tailWord_2590962 prefixEnd_2590962 1330408863534597082959389 := by
  unfold tailWord_2590962
  simp only [CollatzResearch.WordTrace]
  refine ⟨23625036909848662481349785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63000098426263099950266093 23625036909848662481349785)
  ·
    refine ⟨17718777682386496861012339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23625036909848662481349785 17718777682386496861012339)
    ·
      refine ⟨26578166523579745291518509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17718777682386496861012339 26578166523579745291518509)
      ·
        refine ⟨9966812446342404484319441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26578166523579745291518509 9966812446342404484319441)
        ·
          refine ⟨7475109334756803363239581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9966812446342404484319441 7475109334756803363239581)
          ·
            refine ⟨2803166000533801261214843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7475109334756803363239581 2803166000533801261214843)
            ·
              refine ⟨4204749000800701891822265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2803166000533801261214843 4204749000800701891822265)
              ·
                refine ⟨3153561750600526418866699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4204749000800701891822265 3153561750600526418866699)
                ·
                  refine ⟨4730342625900789628300049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3153561750600526418866699 4730342625900789628300049)
                  ·
                    refine ⟨3547756969425592221225037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4730342625900789628300049 3547756969425592221225037)
                    ·
                      refine ⟨1330408863534597082959389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3547756969425592221225037 1330408863534597082959389)
                      ·
                        rfl

theorem cell23_2590962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_2590962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2590962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2590962 prefixEnd_2590962 := by exact prefixLift 2590962
  have htrace : WordTrace (prefixWord ++ tailWord_2590962) baseStart_2590962 baseEnd_2590962 := by
    simpa [prefixWord, tailWord_2590962, baseEnd_2590962] using wordTrace_append hprefix tailTrace_2590962
  have hstable : (prefixWord ++ tailWord_2590962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2590962).length < 2 ^ (prefixWord ++ tailWord_2590962).sum := by decide
  have hdescent : baseEnd_2590962 < baseStart_2590962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2590962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591008 : List Nat := [2, 1, 1, 5, 2, 2, 1, 1, 2, 6]
def baseStart_2591008 : Nat := 118140960795 + 2591008 * 2 ^ 59
def prefixEnd_2591008 : Nat := 4983230072969 + 3 ^ 40 * 2591008 * 2
def baseEnd_2591008 : Nat := 443477494548234634328059

theorem tailTrace_2591008 : CollatzResearch.WordTrace tailWord_2591008 prefixEnd_2591008 443477494548234634328059 := by
  unfold tailWord_2591008
  simp only [CollatzResearch.WordTrace]
  refine ⟨47250912698613999890786839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63001216931485333187715785 47250912698613999890786839)
  ·
    refine ⟨70876369047920999836180259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47250912698613999890786839 70876369047920999836180259)
    ·
      refine ⟨106314553571881499754270389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70876369047920999836180259 106314553571881499754270389)
      ·
        refine ⟨9966989397363890601962849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 106314553571881499754270389 9966989397363890601962849)
        ·
          refine ⟨7475242048022917951472137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9966989397363890601962849 7475242048022917951472137)
          ·
            refine ⟨5606431536017188463604103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7475242048022917951472137 5606431536017188463604103)
            ·
              refine ⟨8409647304025782695406155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5606431536017188463604103 8409647304025782695406155)
              ·
                refine ⟨12614470956038674043109233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8409647304025782695406155 12614470956038674043109233)
                ·
                  refine ⟨9460853217029005532331925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12614470956038674043109233 9460853217029005532331925)
                  ·
                    refine ⟨443477494548234634328059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9460853217029005532331925 443477494548234634328059)
                    ·
                      rfl

theorem cell23_2591008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 2, 6].length) (baseStart_2591008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2591008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2591008 prefixEnd_2591008 := by exact prefixLift 2591008
  have htrace : WordTrace (prefixWord ++ tailWord_2591008) baseStart_2591008 baseEnd_2591008 := by
    simpa [prefixWord, tailWord_2591008, baseEnd_2591008] using wordTrace_append hprefix tailTrace_2591008
  have hstable : (prefixWord ++ tailWord_2591008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591008).length < 2 ^ (prefixWord ++ tailWord_2591008).sum := by decide
  have hdescent : baseEnd_2591008 < baseStart_2591008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591048 : List Nat := [2, 1, 3, 1, 1, 2, 3, 2, 2, 3, 3]
def baseStart_2591048 : Nat := 118140960795 + 2591048 * 2 ^ 59
def prefixEnd_2591048 : Nat := 4983230072969 + 3 ^ 40 * 2591048 * 2
def baseEnd_2591048 : Nat := 1330453022870883746483993

theorem tailTrace_2591048 : CollatzResearch.WordTrace tailWord_2591048 prefixEnd_2591048 1330453022870883746483993 := by
  unfold tailWord_2591048
  simp only [CollatzResearch.WordTrace]
  refine ⟨47251642158541543306514899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63002189544722057742019865 47251642158541543306514899)
  ·
    refine ⟨70877463237812314959772349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47251642158541543306514899 70877463237812314959772349)
    ·
      refine ⟨26579048714179618109914631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70877463237812314959772349 26579048714179618109914631)
      ·
        refine ⟨39868573071269427164871947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26579048714179618109914631 39868573071269427164871947)
        ·
          refine ⟨59802859606904140747307921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39868573071269427164871947 59802859606904140747307921)
          ·
            refine ⟨44852144705178105560480941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59802859606904140747307921 44852144705178105560480941)
            ·
              refine ⟨16819554264441789585180353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44852144705178105560480941 16819554264441789585180353)
              ·
                refine ⟨12614665698331342188885265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16819554264441789585180353 12614665698331342188885265)
                ·
                  refine ⟨9460999273748506641663949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12614665698331342188885265 9460999273748506641663949)
                  ·
                    refine ⟨3547874727655689990623981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9460999273748506641663949 3547874727655689990623981)
                    ·
                      refine ⟨1330453022870883746483993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3547874727655689990623981 1330453022870883746483993)
                      ·
                        rfl

theorem cell23_2591048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 2, 3, 3].length) (baseStart_2591048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2591048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2591048 prefixEnd_2591048 := by exact prefixLift 2591048
  have htrace : WordTrace (prefixWord ++ tailWord_2591048) baseStart_2591048 baseEnd_2591048 := by
    simpa [prefixWord, tailWord_2591048, baseEnd_2591048] using wordTrace_append hprefix tailTrace_2591048
  have hstable : (prefixWord ++ tailWord_2591048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591048).length < 2 ^ (prefixWord ++ tailWord_2591048).sum := by decide
  have hdescent : baseEnd_2591048 < baseStart_2591048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591070 : List Nat := [4, 4, 2, 1, 1, 1, 2, 2, 1, 3, 2]
def baseStart_2591070 : Nat := 118140960795 + 2591070 * 2 ^ 59
def prefixEnd_2591070 : Nat := 4983230072969 + 3 ^ 40 * 2591070 * 2
def baseEnd_2591070 : Nat := 1330464319445282660408893

theorem tailTrace_2591070 : CollatzResearch.WordTrace tailWord_2591070 prefixEnd_2591070 1330464319445282660408893 := by
  unfold tailWord_2591070
  simp only [CollatzResearch.WordTrace]
  refine ⟨11813010840375423046291333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63002724482002256246887109 11813010840375423046291333)
  ·
    refine ⟨2214939532570391821179625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11813010840375423046291333 2214939532570391821179625)
    ·
      refine ⟨1661204649427793865884719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2214939532570391821179625 1661204649427793865884719)
      ·
        refine ⟨2491806974141690798827079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1661204649427793865884719 2491806974141690798827079)
        ·
          refine ⟨3737710461212536198240619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2491806974141690798827079 3737710461212536198240619)
          ·
            refine ⟨5606565691818804297360929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3737710461212536198240619 5606565691818804297360929)
            ·
              refine ⟨4204924268864103223020697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5606565691818804297360929 4204924268864103223020697)
              ·
                refine ⟨3153693201648077417265523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4204924268864103223020697 3153693201648077417265523)
                ·
                  refine ⟨4730539802472116125898285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3153693201648077417265523 4730539802472116125898285)
                  ·
                    refine ⟨1773952425927043547211857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4730539802472116125898285 1773952425927043547211857)
                    ·
                      refine ⟨1330464319445282660408893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1773952425927043547211857 1330464319445282660408893)
                      ·
                        rfl

theorem cell23_2591070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_2591070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2591070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2591070 prefixEnd_2591070 := by exact prefixLift 2591070
  have htrace : WordTrace (prefixWord ++ tailWord_2591070) baseStart_2591070 baseEnd_2591070 := by
    simpa [prefixWord, tailWord_2591070, baseEnd_2591070] using wordTrace_append hprefix tailTrace_2591070
  have hstable : (prefixWord ++ tailWord_2591070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591070).length < 2 ^ (prefixWord ++ tailWord_2591070).sum := by decide
  have hdescent : baseEnd_2591070 < baseStart_2591070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591081 : List Nat := [1, 2, 1, 1, 1, 3, 3, 1, 2, 8]
def baseStart_2591081 : Nat := 118140960795 + 2591081 * 2 ^ 59
def prefixEnd_2591081 : Nat := 4983230072969 + 3 ^ 40 * 2591081 * 2
def baseEnd_2591081 : Nat := 443489989244160705790447

theorem tailTrace_2591081 : CollatzResearch.WordTrace tailWord_2591081 prefixEnd_2591081 443489989244160705790447 := by
  unfold tailWord_2591081
  simp only [CollatzResearch.WordTrace]
  refine ⟨94504487925963533248981097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63002991950642355499320731 94504487925963533248981097)
  ·
    refine ⟨70878365944472649936735823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94504487925963533248981097 70878365944472649936735823)
    ·
      refine ⟨106317548916708974905103735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70878365944472649936735823 106317548916708974905103735)
      ·
        refine ⟨159476323375063462357655603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106317548916708974905103735 159476323375063462357655603)
        ·
          refine ⟨239214485062595193536483405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159476323375063462357655603 239214485062595193536483405)
          ·
            refine ⟨89705431898473197576181277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 239214485062595193536483405 89705431898473197576181277)
            ·
              refine ⟨33639536961927449091067979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89705431898473197576181277 33639536961927449091067979)
              ·
                refine ⟨50459305442891173636601969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33639536961927449091067979 50459305442891173636601969)
                ·
                  refine ⟨37844479082168380227451477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50459305442891173636601969 37844479082168380227451477)
                  ·
                    refine ⟨443489989244160705790447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 37844479082168380227451477 443489989244160705790447)
                    ·
                      rfl

theorem cell23_2591081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 8].length) (baseStart_2591081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2591081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2591081 prefixEnd_2591081 := by exact prefixLift 2591081
  have htrace : WordTrace (prefixWord ++ tailWord_2591081) baseStart_2591081 baseEnd_2591081 := by
    simpa [prefixWord, tailWord_2591081, baseEnd_2591081] using wordTrace_append hprefix tailTrace_2591081
  have hstable : (prefixWord ++ tailWord_2591081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591081).length < 2 ^ (prefixWord ++ tailWord_2591081).sum := by decide
  have hdescent : baseEnd_2591081 < baseStart_2591081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591088 : List Nat := [2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 4]
def baseStart_2591088 : Nat := 118140960795 + 2591088 * 2 ^ 59
def prefixEnd_2591088 : Nat := 4983230072969 + 3 ^ 40 * 2591088 * 2
def baseEnd_2591088 : Nat := 1330473562097063589983809

theorem tailTrace_2591088 : CollatzResearch.WordTrace tailWord_2591088 prefixEnd_2591088 1330473562097063589983809 := by
  unfold tailWord_2591088
  simp only [CollatzResearch.WordTrace]
  refine ⟨47252371618469086722242959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63003162157958782296323945 47252371618469086722242959)
  ·
    refine ⟨70878557427703630083364439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47252371618469086722242959 70878557427703630083364439)
    ·
      refine ⟨106317836141555445125046659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70878557427703630083364439 106317836141555445125046659)
      ·
        refine ⟨159476754212333167687569989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106317836141555445125046659 159476754212333167687569989)
        ·
          refine ⟨29901891414812468941419373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 159476754212333167687569989 29901891414812468941419373)
          ·
            refine ⟨11213209280554675853032265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29901891414812468941419373 11213209280554675853032265)
            ·
              refine ⟨8409906960416006889774199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11213209280554675853032265 8409906960416006889774199)
              ·
                refine ⟨12614860440624010334661299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8409906960416006889774199 12614860440624010334661299)
                ·
                  refine ⟨18922290660936015501991949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12614860440624010334661299 18922290660936015501991949)
                  ·
                    refine ⟨7095858997851005813246981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18922290660936015501991949 7095858997851005813246981)
                    ·
                      refine ⟨1330473562097063589983809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7095858997851005813246981 1330473562097063589983809)
                      ·
                        rfl

theorem cell23_2591088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 4].length) (baseStart_2591088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2591088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2591088 prefixEnd_2591088 := by exact prefixLift 2591088
  have htrace : WordTrace (prefixWord ++ tailWord_2591088) baseStart_2591088 baseEnd_2591088 := by
    simpa [prefixWord, tailWord_2591088, baseEnd_2591088] using wordTrace_append hprefix tailTrace_2591088
  have hstable : (prefixWord ++ tailWord_2591088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591088).length < 2 ^ (prefixWord ++ tailWord_2591088).sum := by decide
  have hdescent : baseEnd_2591088 < baseStart_2591088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591105 : List Nat := [1, 2, 4, 3, 1, 1, 1, 1, 4, 1, 4]
def baseStart_2591105 : Nat := 118140960795 + 2591105 * 2 ^ 59
def prefixEnd_2591105 : Nat := 4983230072969 + 3 ^ 40 * 2591105 * 2
def baseEnd_2591105 : Nat := 1330482291268190023471231

theorem tailTrace_2591105 : CollatzResearch.WordTrace tailWord_2591105 prefixEnd_2591105 1330482291268190023471231 := by
  unfold tailWord_2591105
  simp only [CollatzResearch.WordTrace]
  refine ⟨94505363277876585347854769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63003575518584390231903179 94505363277876585347854769)
  ·
    refine ⟨70879022458407439010891077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94505363277876585347854769 70879022458407439010891077)
    ·
      refine ⟨13289816710951394814542077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70879022458407439010891077 13289816710951394814542077)
      ·
        refine ⟨4983681266606773055453279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13289816710951394814542077 4983681266606773055453279)
        ·
          refine ⟨7475521899910159583179919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4983681266606773055453279 7475521899910159583179919)
          ·
            refine ⟨11213282849865239374769879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7475521899910159583179919 11213282849865239374769879)
            ·
              refine ⟨16819924274797859062154819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11213282849865239374769879 16819924274797859062154819)
              ·
                refine ⟨25229886412196788593232229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16819924274797859062154819 25229886412196788593232229)
                ·
                  refine ⟨4730603702286897861231043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25229886412196788593232229 4730603702286897861231043)
                  ·
                    refine ⟨7095905553430346791846565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4730603702286897861231043 7095905553430346791846565)
                    ·
                      refine ⟨1330482291268190023471231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7095905553430346791846565 1330482291268190023471231)
                      ·
                        rfl

theorem cell23_2591105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_2591105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2591105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2591105 prefixEnd_2591105 := by exact prefixLift 2591105
  have htrace : WordTrace (prefixWord ++ tailWord_2591105) baseStart_2591105 baseEnd_2591105 := by
    simpa [prefixWord, tailWord_2591105, baseEnd_2591105] using wordTrace_append hprefix tailTrace_2591105
  have hstable : (prefixWord ++ tailWord_2591105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591105).length < 2 ^ (prefixWord ++ tailWord_2591105).sum := by decide
  have hdescent : baseEnd_2591105 < baseStart_2591105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591106 : List Nat := [3, 4, 2, 1, 2, 1, 3, 2, 5]
def baseStart_2591106 : Nat := 118140960795 + 2591106 * 2 ^ 59
def prefixEnd_2591106 : Nat := 4983230072969 + 3 ^ 40 * 2591106 * 2
def baseEnd_2591106 : Nat := 147831422749871613284303

theorem tailTrace_2591106 : CollatzResearch.WordTrace tailWord_2591106 prefixEnd_2591106 147831422749871613284303 := by
  unfold tailWord_2591106
  simp only [CollatzResearch.WordTrace]
  refine ⟨23626349937718240629660293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63003599833915308345760781 23626349937718240629660293)
  ·
    refine ⟨4429940613322170118061305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23626349937718240629660293 4429940613322170118061305)
    ·
      refine ⟨3322455459991627588545979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4429940613322170118061305 3322455459991627588545979)
      ·
        refine ⟨4983683189987441382818969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3322455459991627588545979 4983683189987441382818969)
        ·
          refine ⟨3737762392490581037114227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4983683189987441382818969 3737762392490581037114227)
          ·
            refine ⟨5606643588735871555671341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3737762392490581037114227 5606643588735871555671341)
            ·
              refine ⟨2102491345775951833376753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5606643588735871555671341 2102491345775951833376753)
              ·
                refine ⟨1576868509331963875032565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2102491345775951833376753 1576868509331963875032565)
                ·
                  refine ⟨147831422749871613284303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1576868509331963875032565 147831422749871613284303)
                  ·
                    rfl

theorem cell23_2591106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_2591106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2591106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2591106 prefixEnd_2591106 := by exact prefixLift 2591106
  have htrace : WordTrace (prefixWord ++ tailWord_2591106) baseStart_2591106 baseEnd_2591106 := by
    simpa [prefixWord, tailWord_2591106, baseEnd_2591106] using wordTrace_append hprefix tailTrace_2591106
  have hstable : (prefixWord ++ tailWord_2591106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591106).length < 2 ^ (prefixWord ++ tailWord_2591106).sum := by decide
  have hdescent : baseEnd_2591106 < baseStart_2591106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591115 : List Nat := [1, 1, 1, 1, 4, 4, 3, 1, 3, 4]
def baseStart_2591115 : Nat := 118140960795 + 2591115 * 2 ^ 59
def prefixEnd_2591115 : Nat := 4983230072969 + 3 ^ 40 * 2591115 * 2
def baseEnd_2591115 : Nat := 443495808691578328115395

theorem tailTrace_2591115 : CollatzResearch.WordTrace tailWord_2591115 prefixEnd_2591115 443495808691578328115395 := by
  unfold tailWord_2591115
  simp only [CollatzResearch.WordTrace]
  refine ⟨94505728007840357055718799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63003818671893571370479199 94505728007840357055718799)
  ·
    refine ⟨141758592011760535583578199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94505728007840357055718799 141758592011760535583578199)
    ·
      refine ⟨212637888017640803375367299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141758592011760535583578199 212637888017640803375367299)
      ·
        refine ⟨318956832026461205063050949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212637888017640803375367299 318956832026461205063050949)
        ·
          refine ⟨59804406004961475949322053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 318956832026461205063050949 59804406004961475949322053)
          ·
            refine ⟨11213326125930276740497885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59804406004961475949322053 11213326125930276740497885)
            ·
              refine ⟨4204997297223853777686707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11213326125930276740497885 4204997297223853777686707)
              ·
                refine ⟨6307495945835780666530061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4204997297223853777686707 6307495945835780666530061)
                ·
                  refine ⟨2365310979688417749948773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6307495945835780666530061 2365310979688417749948773)
                  ·
                    refine ⟨443495808691578328115395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2365310979688417749948773 443495808691578328115395)
                    ·
                      rfl

theorem cell23_2591115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 3, 4].length) (baseStart_2591115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2591115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2591115 prefixEnd_2591115 := by exact prefixLift 2591115
  have htrace : WordTrace (prefixWord ++ tailWord_2591115) baseStart_2591115 baseEnd_2591115 := by
    simpa [prefixWord, tailWord_2591115, baseEnd_2591115] using wordTrace_append hprefix tailTrace_2591115
  have hstable : (prefixWord ++ tailWord_2591115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591115).length < 2 ^ (prefixWord ++ tailWord_2591115).sum := by decide
  have hdescent : baseEnd_2591115 < baseStart_2591115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591199 : List Nat := [1, 1, 2, 3, 3, 4, 1, 1, 2, 3, 2]
def baseStart_2591199 : Nat := 118140960795 + 2591199 * 2 ^ 59
def prefixEnd_2591199 : Nat := 4983230072969 + 3 ^ 40 * 2591199 * 2
def baseEnd_2591199 : Nat := 1330530558449712655695799

theorem tailTrace_2591199 : CollatzResearch.WordTrace tailWord_2591199 prefixEnd_2591199 1330530558449712655695799 := by
  unfold tailWord_2591199
  simp only [CollatzResearch.WordTrace]
  refine ⟨94508791739536039401776651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63005861159690692934517767 94508791739536039401776651)
  ·
    refine ⟨141763187609304059102664977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94508791739536039401776651 141763187609304059102664977)
    ·
      refine ⟨106322390706978044326998733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141763187609304059102664977 106322390706978044326998733)
      ·
        refine ⟨39870896515116766622624525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106322390706978044326998733 39870896515116766622624525)
        ·
          refine ⟨14951586193168787483484197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39870896515116766622624525 14951586193168787483484197)
          ·
            refine ⟨2803422411219147653153287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14951586193168787483484197 2803422411219147653153287)
            ·
              refine ⟨4205133616828721479729931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2803422411219147653153287 4205133616828721479729931)
              ·
                refine ⟨6307700425243082219594897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4205133616828721479729931 6307700425243082219594897)
                ·
                  refine ⟨4730775318932311664696173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6307700425243082219594897 4730775318932311664696173)
                  ·
                    refine ⟨1774040744599616874261065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4730775318932311664696173 1774040744599616874261065)
                    ·
                      refine ⟨1330530558449712655695799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1774040744599616874261065 1330530558449712655695799)
                      ·
                        rfl

theorem cell23_2591199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 1, 2, 3, 2].length) (baseStart_2591199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2591199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2591199 prefixEnd_2591199 := by exact prefixLift 2591199
  have htrace : WordTrace (prefixWord ++ tailWord_2591199) baseStart_2591199 baseEnd_2591199 := by
    simpa [prefixWord, tailWord_2591199, baseEnd_2591199] using wordTrace_append hprefix tailTrace_2591199
  have hstable : (prefixWord ++ tailWord_2591199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591199).length < 2 ^ (prefixWord ++ tailWord_2591199).sum := by decide
  have hdescent : baseEnd_2591199 < baseStart_2591199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591212 : List Nat := [2, 2, 1, 1, 2, 1, 3, 2, 5, 2, 2]
def baseStart_2591212 : Nat := 118140960795 + 2591212 * 2 ^ 59
def prefixEnd_2591212 : Nat := 4983230072969 + 3 ^ 40 * 2591212 * 2
def baseEnd_2591212 : Nat := 1330537233698221104833239

theorem tailTrace_2591212 : CollatzResearch.WordTrace tailWord_2591212 prefixEnd_2591212 1330537233698221104833239 := by
  unfold tailWord_2591212
  simp only [CollatzResearch.WordTrace]
  refine ⟨47254632944244471310999945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63006177258992628414666593 47254632944244471310999945)
  ·
    refine ⟨35440974708183353483249959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47254632944244471310999945 35440974708183353483249959)
    ·
      refine ⟨53161462062275030224874939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35440974708183353483249959 53161462062275030224874939)
      ·
        refine ⟨79742193093412545337312409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53161462062275030224874939 79742193093412545337312409)
        ·
          refine ⟨59806644820059409002984307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79742193093412545337312409 59806644820059409002984307)
          ·
            refine ⟨89709967230089113504476461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59806644820059409002984307 89709967230089113504476461)
            ·
              refine ⟨33641237711283417564178673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89709967230089113504476461 33641237711283417564178673)
              ·
                refine ⟨25230928283462563173134005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33641237711283417564178673 25230928283462563173134005)
                ·
                  refine ⟨2365399526574615297481313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25230928283462563173134005 2365399526574615297481313)
                  ·
                    refine ⟨1774049644930961473110985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2365399526574615297481313 1774049644930961473110985)
                    ·
                      refine ⟨1330537233698221104833239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1774049644930961473110985 1330537233698221104833239)
                      ·
                        rfl

theorem cell23_2591212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 2, 2].length) (baseStart_2591212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2591212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2591212 prefixEnd_2591212 := by exact prefixLift 2591212
  have htrace : WordTrace (prefixWord ++ tailWord_2591212) baseStart_2591212 baseEnd_2591212 := by
    simpa [prefixWord, tailWord_2591212, baseEnd_2591212] using wordTrace_append hprefix tailTrace_2591212
  have hstable : (prefixWord ++ tailWord_2591212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591212).length < 2 ^ (prefixWord ++ tailWord_2591212).sum := by decide
  have hdescent : baseEnd_2591212 < baseStart_2591212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591222 : List Nat := [5, 1, 1, 1, 2, 1, 3, 1, 4, 4]
def baseStart_2591222 : Nat := 118140960795 + 2591222 * 2 ^ 59
def prefixEnd_2591222 : Nat := 4983230072969 + 3 ^ 40 * 2591222 * 2
def baseEnd_2591222 : Nat := 443514122834922021902731

theorem tailTrace_2591222 : CollatzResearch.WordTrace tailWord_2591222 prefixEnd_2591222 443514122834922021902731 := by
  unfold tailWord_2591222
  simp only [CollatzResearch.WordTrace]
  refine ⟨5906851913653294645616495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63006420412301809553242613 5906851913653294645616495)
  ·
    refine ⟨8860277870479941968424743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5906851913653294645616495 8860277870479941968424743)
    ·
      refine ⟨13290416805719912952637115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8860277870479941968424743 13290416805719912952637115)
      ·
        refine ⟨19935625208579869428955673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13290416805719912952637115 19935625208579869428955673)
        ·
          refine ⟨14951718906434902071716755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19935625208579869428955673 14951718906434902071716755)
          ·
            refine ⟨22427578359652353107575133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14951718906434902071716755 22427578359652353107575133)
            ·
              refine ⟨8410341884869632415340675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22427578359652353107575133 8410341884869632415340675)
              ·
                refine ⟨12615512827304448623011013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8410341884869632415340675 12615512827304448623011013)
                ·
                  refine ⟨2365408655119584116814565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12615512827304448623011013 2365408655119584116814565)
                  ·
                    refine ⟨443514122834922021902731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2365408655119584116814565 443514122834922021902731)
                    ·
                      rfl

theorem cell23_2591222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_2591222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2591222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2591222 prefixEnd_2591222 := by exact prefixLift 2591222
  have htrace : WordTrace (prefixWord ++ tailWord_2591222) baseStart_2591222 baseEnd_2591222 := by
    simpa [prefixWord, tailWord_2591222, baseEnd_2591222] using wordTrace_append hprefix tailTrace_2591222
  have hstable : (prefixWord ++ tailWord_2591222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591222).length < 2 ^ (prefixWord ++ tailWord_2591222).sum := by decide
  have hdescent : baseEnd_2591222 < baseStart_2591222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591228 : List Nat := [2, 2, 2, 1, 2, 1, 1, 1, 2, 2, 7]
def baseStart_2591228 : Nat := 118140960795 + 2591228 * 2 ^ 59
def prefixEnd_2591228 : Nat := 4983230072969 + 3 ^ 40 * 2591228 * 2
def baseEnd_2591228 : Nat := 1330545449388693042233165

theorem tailTrace_2591228 : CollatzResearch.WordTrace tailWord_2591228 prefixEnd_2591228 1330545449388693042233165 := by
  unfold tailWord_2591228
  simp only [CollatzResearch.WordTrace]
  refine ⟨47254924728215488677291169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63006566304287318236388225 47254924728215488677291169)
  ·
    refine ⟨35441193546161616507968377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47254924728215488677291169 35441193546161616507968377)
    ·
      refine ⟨26580895159621212380976283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35441193546161616507968377 26580895159621212380976283)
      ·
        refine ⟨39871342739431818571464425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26580895159621212380976283 39871342739431818571464425)
        ·
          refine ⟨29903507054573863928598319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39871342739431818571464425 29903507054573863928598319)
          ·
            refine ⟨44855260581860795892897479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29903507054573863928598319 44855260581860795892897479)
            ·
              refine ⟨67282890872791193839346219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44855260581860795892897479 67282890872791193839346219)
              ·
                refine ⟨100924336309186790759019329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67282890872791193839346219 100924336309186790759019329)
                ·
                  refine ⟨75693252231890093069264497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100924336309186790759019329 75693252231890093069264497)
                  ·
                    refine ⟨56769939173917569801948373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 75693252231890093069264497 56769939173917569801948373)
                    ·
                      refine ⟨1330545449388693042233165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 56769939173917569801948373 1330545449388693042233165)
                      ·
                        rfl

theorem cell23_2591228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_2591228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2591228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2591228 prefixEnd_2591228 := by exact prefixLift 2591228
  have htrace : WordTrace (prefixWord ++ tailWord_2591228) baseStart_2591228 baseEnd_2591228 := by
    simpa [prefixWord, tailWord_2591228, baseEnd_2591228] using wordTrace_append hprefix tailTrace_2591228
  have hstable : (prefixWord ++ tailWord_2591228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591228).length < 2 ^ (prefixWord ++ tailWord_2591228).sum := by decide
  have hdescent : baseEnd_2591228 < baseStart_2591228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591229 : List Nat := [1, 4, 1, 1, 1, 3, 4, 1, 3, 2, 2]
def baseStart_2591229 : Nat := 118140960795 + 2591229 * 2 ^ 59
def prefixEnd_2591229 : Nat := 4983230072969 + 3 ^ 40 * 2591229 * 2
def baseEnd_2591229 : Nat := 1330545962869347538320661

theorem tailTrace_2591229 : CollatzResearch.WordTrace tailWord_2591229 prefixEnd_2591229 1330545962869347538320661 := by
  unfold tailWord_2591229
  simp only [CollatzResearch.WordTrace]
  refine ⟨94509885929427354525368741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63006590619618236350245827 94509885929427354525368741)
  ·
    refine ⟨17720603611767628973506639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94509885929427354525368741 17720603611767628973506639)
    ·
      refine ⟨26580905417651443460259959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17720603611767628973506639 26580905417651443460259959)
      ·
        refine ⟨39871358126477165190389939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26580905417651443460259959 39871358126477165190389939)
        ·
          refine ⟨59807037189715747785584909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39871358126477165190389939 59807037189715747785584909)
          ·
            refine ⟨22427638946143405419594341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59807037189715747785584909 22427638946143405419594341)
            ·
              refine ⟨4205182302401888516173939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22427638946143405419594341 4205182302401888516173939)
              ·
                refine ⟨6307773453602832774260909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4205182302401888516173939 6307773453602832774260909)
                ·
                  refine ⟨2365415045101062290347841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6307773453602832774260909 2365415045101062290347841)
                  ·
                    refine ⟨1774061283825796717760881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2365415045101062290347841 1774061283825796717760881)
                    ·
                      refine ⟨1330545962869347538320661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1774061283825796717760881 1330545962869347538320661)
                      ·
                        rfl

theorem cell23_2591229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 1, 3, 2, 2].length) (baseStart_2591229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2591229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2591229 prefixEnd_2591229 := by exact prefixLift 2591229
  have htrace : WordTrace (prefixWord ++ tailWord_2591229) baseStart_2591229 baseEnd_2591229 := by
    simpa [prefixWord, tailWord_2591229, baseEnd_2591229] using wordTrace_append hprefix tailTrace_2591229
  have hstable : (prefixWord ++ tailWord_2591229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591229).length < 2 ^ (prefixWord ++ tailWord_2591229).sum := by decide
  have hdescent : baseEnd_2591229 < baseStart_2591229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591239 : List Nat := [1, 1, 4, 3, 4, 1, 1, 1, 1, 6]
def baseStart_2591239 : Nat := 118140960795 + 2591239 * 2 ^ 59
def prefixEnd_2591239 : Nat := 4983230072969 + 3 ^ 40 * 2591239 * 2
def baseEnd_2591239 : Nat := 443517032558630833065205

theorem tailTrace_2591239 : CollatzResearch.WordTrace tailWord_2591239 prefixEnd_2591239 443517032558630833065205 := by
  unfold tailWord_2591239
  simp only [CollatzResearch.WordTrace]
  refine ⟨94510250659391126233232771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63006833772927417488821847 94510250659391126233232771)
  ·
    refine ⟨141765375989086689349849157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94510250659391126233232771 141765375989086689349849157)
    ·
      refine ⟨26581007997953754253096717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141765375989086689349849157 26581007997953754253096717)
      ·
        refine ⟨9967877999232657844911269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26581007997953754253096717 9967877999232657844911269)
        ·
          refine ⟨1868977124856123345920863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9967877999232657844911269 1868977124856123345920863)
          ·
            refine ⟨2803465687284185018881295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1868977124856123345920863 2803465687284185018881295)
            ·
              refine ⟨4205198530926277528321943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2803465687284185018881295 4205198530926277528321943)
              ·
                refine ⟨6307797796389416292482915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4205198530926277528321943 6307797796389416292482915)
                ·
                  refine ⟨9461696694584124438724373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6307797796389416292482915 9461696694584124438724373)
                  ·
                    refine ⟨443517032558630833065205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9461696694584124438724373 443517032558630833065205)
                    ·
                      rfl

theorem cell23_2591239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 1, 1, 6].length) (baseStart_2591239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2591239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2591239 prefixEnd_2591239 := by exact prefixLift 2591239
  have htrace : WordTrace (prefixWord ++ tailWord_2591239) baseStart_2591239 baseEnd_2591239 := by
    simpa [prefixWord, tailWord_2591239, baseEnd_2591239] using wordTrace_append hprefix tailTrace_2591239
  have hstable : (prefixWord ++ tailWord_2591239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591239).length < 2 ^ (prefixWord ++ tailWord_2591239).sum := by decide
  have hdescent : baseEnd_2591239 < baseStart_2591239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591252 : List Nat := [2, 4, 3, 1, 1, 2, 1, 9]
def baseStart_2591252 : Nat := 118140960795 + 2591252 * 2 ^ 59
def prefixEnd_2591252 : Nat := 4983230072969 + 3 ^ 40 * 2591252 * 2
def baseEnd_2591252 : Nat := 49279917515718553641965

theorem tailTrace_2591252 : CollatzResearch.WordTrace tailWord_2591252 prefixEnd_2591252 49279917515718553641965 := by
  unfold tailWord_2591252
  simp only [CollatzResearch.WordTrace]
  refine ⟨47255362404172014726728005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63007149872229352968970673 47255362404172014726728005)
  ·
    refine ⟨8860380450782252761261501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47255362404172014726728005 8860380450782252761261501)
    ·
      refine ⟨3322642669043344785473063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8860380450782252761261501 3322642669043344785473063)
      ·
        refine ⟨4983964003565017178209595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3322642669043344785473063 4983964003565017178209595)
        ·
          refine ⟨7475946005347525767314393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4983964003565017178209595 7475946005347525767314393)
          ·
            refine ⟨5606959504010644325485795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7475946005347525767314393 5606959504010644325485795)
            ·
              refine ⟨8410439256015966488228693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5606959504010644325485795 8410439256015966488228693)
              ·
                refine ⟨49279917515718553641965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8410439256015966488228693 49279917515718553641965)
                ·
                  rfl

theorem cell23_2591252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 9].length) (baseStart_2591252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2591252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2591252 prefixEnd_2591252 := by exact prefixLift 2591252
  have htrace : WordTrace (prefixWord ++ tailWord_2591252) baseStart_2591252 baseEnd_2591252 := by
    simpa [prefixWord, tailWord_2591252, baseEnd_2591252] using wordTrace_append hprefix tailTrace_2591252
  have hstable : (prefixWord ++ tailWord_2591252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591252).length < 2 ^ (prefixWord ++ tailWord_2591252).sum := by decide
  have hdescent : baseEnd_2591252 < baseStart_2591252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591285 : List Nat := [1, 3, 3, 1, 1, 2, 2, 1, 2, 3, 4]
def baseStart_2591285 : Nat := 118140960795 + 2591285 * 2 ^ 59
def prefixEnd_2591285 : Nat := 4983230072969 + 3 ^ 40 * 2591285 * 2
def baseEnd_2591285 : Nat := 1330574717785999319220403

theorem tailTrace_2591285 : CollatzResearch.WordTrace tailWord_2591285 prefixEnd_2591285 1330574717785999319220403 := by
  unfold tailWord_2591285
  simp only [CollatzResearch.WordTrace]
  refine ⟨94511928417224476089407309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63007952278149650726271539 94511928417224476089407309)
  ·
    refine ⟨35441973156459178533527741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94511928417224476089407309 35441973156459178533527741)
    ·
      refine ⟨13290739933672191950072903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35441973156459178533527741 13290739933672191950072903)
      ·
        refine ⟨19936109900508287925109355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13290739933672191950072903 19936109900508287925109355)
        ·
          refine ⟨29904164850762431887664033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19936109900508287925109355 29904164850762431887664033)
          ·
            refine ⟨22428123638071823915748025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29904164850762431887664033 22428123638071823915748025)
            ·
              refine ⟨16821092728553867936811019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22428123638071823915748025 16821092728553867936811019)
              ·
                refine ⟨25231639092830801905216529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16821092728553867936811019 25231639092830801905216529)
                ·
                  refine ⟨18923729319623101428912397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25231639092830801905216529 18923729319623101428912397)
                  ·
                    refine ⟨7096398494858663035842149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18923729319623101428912397 7096398494858663035842149)
                    ·
                      refine ⟨1330574717785999319220403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7096398494858663035842149 1330574717785999319220403)
                      ·
                        rfl

theorem cell23_2591285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_2591285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2591285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2591285 prefixEnd_2591285 := by exact prefixLift 2591285
  have htrace : WordTrace (prefixWord ++ tailWord_2591285) baseStart_2591285 baseEnd_2591285 := by
    simpa [prefixWord, tailWord_2591285, baseEnd_2591285] using wordTrace_append hprefix tailTrace_2591285
  have hstable : (prefixWord ++ tailWord_2591285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591285).length < 2 ^ (prefixWord ++ tailWord_2591285).sum := by decide
  have hdescent : baseEnd_2591285 < baseStart_2591285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591300 : List Nat := [2, 3, 5, 1, 1, 2, 1, 2, 1, 2, 3]
def baseStart_2591300 : Nat := 118140960795 + 2591300 * 2 ^ 59
def prefixEnd_2591300 : Nat := 4983230072969 + 3 ^ 40 * 2591300 * 2
def baseEnd_2591300 : Nat := 1330582419995816760532835

theorem tailTrace_2591300 : CollatzResearch.WordTrace tailWord_2591300 prefixEnd_2591300 1330582419995816760532835 := by
  unfold tailWord_2591300
  simp only [CollatzResearch.WordTrace]
  refine ⟨47256237756085066825601677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63008317008113422434135569 47256237756085066825601677)
  ·
    refine ⟨17721089158531900059600629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47256237756085066825601677 17721089158531900059600629)
    ·
      refine ⟨1661352108612365630587559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17721089158531900059600629 1661352108612365630587559)
      ·
        refine ⟨2492028162918548445881339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1661352108612365630587559 2492028162918548445881339)
        ·
          refine ⟨3738042244377822668822009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2492028162918548445881339 3738042244377822668822009)
          ·
            refine ⟨2803531683283367001616507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3738042244377822668822009 2803531683283367001616507)
            ·
              refine ⟨4205297524925050502424761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2803531683283367001616507 4205297524925050502424761)
              ·
                refine ⟨3153973143693787876818571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4205297524925050502424761 3153973143693787876818571)
                ·
                  refine ⟨4730959715540681815227857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3153973143693787876818571 4730959715540681815227857)
                  ·
                    refine ⟨3548219786655511361420893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4730959715540681815227857 3548219786655511361420893)
                    ·
                      refine ⟨1330582419995816760532835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3548219786655511361420893 1330582419995816760532835)
                      ·
                        rfl

theorem cell23_2591300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_2591300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2591300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2591300 prefixEnd_2591300 := by exact prefixLift 2591300
  have htrace : WordTrace (prefixWord ++ tailWord_2591300) baseStart_2591300 baseEnd_2591300 := by
    simpa [prefixWord, tailWord_2591300, baseEnd_2591300] using wordTrace_append hprefix tailTrace_2591300
  have hstable : (prefixWord ++ tailWord_2591300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591300).length < 2 ^ (prefixWord ++ tailWord_2591300).sum := by decide
  have hdescent : baseEnd_2591300 < baseStart_2591300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591306 : List Nat := [3, 1, 2, 1, 1, 6, 1, 2, 1, 3, 2]
def baseStart_2591306 : Nat := 118140960795 + 2591306 * 2 ^ 59
def prefixEnd_2591306 : Nat := 4983230072969 + 3 ^ 40 * 2591306 * 2
def baseEnd_2591306 : Nat := 1330585500879743737057807

theorem tailTrace_2591306 : CollatzResearch.WordTrace tailWord_2591306 prefixEnd_2591306 1330585500879743737057807 := by
  unfold tailWord_2591306
  simp only [CollatzResearch.WordTrace]
  refine ⟨23628173587537099168980443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63008462900098931117281181 23628173587537099168980443)
  ·
    refine ⟨35442260381305648753470665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23628173587537099168980443 35442260381305648753470665)
    ·
      refine ⟨26581695285979236565102999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35442260381305648753470665 26581695285979236565102999)
      ·
        refine ⟨39872542928968854847654499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26581695285979236565102999 39872542928968854847654499)
        ·
          refine ⟨59808814393453282271481749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39872542928968854847654499 59808814393453282271481749)
          ·
            refine ⟨2803538174693122606475707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 59808814393453282271481749 2803538174693122606475707)
            ·
              refine ⟨4205307262039683909713561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2803538174693122606475707 4205307262039683909713561)
              ·
                refine ⟨3153980446529762932285171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4205307262039683909713561 3153980446529762932285171)
                ·
                  refine ⟨4730970669794644398427757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3153980446529762932285171 4730970669794644398427757)
                  ·
                    refine ⟨1774114001172991649410409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4730970669794644398427757 1774114001172991649410409)
                    ·
                      refine ⟨1330585500879743737057807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1774114001172991649410409 1330585500879743737057807)
                      ·
                        rfl

theorem cell23_2591306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 2, 1, 3, 2].length) (baseStart_2591306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2591306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2591306 prefixEnd_2591306 := by exact prefixLift 2591306
  have htrace : WordTrace (prefixWord ++ tailWord_2591306) baseStart_2591306 baseEnd_2591306 := by
    simpa [prefixWord, tailWord_2591306, baseEnd_2591306] using wordTrace_append hprefix tailTrace_2591306
  have hstable : (prefixWord ++ tailWord_2591306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591306).length < 2 ^ (prefixWord ++ tailWord_2591306).sum := by decide
  have hdescent : baseEnd_2591306 < baseStart_2591306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591349 : List Nat := [1, 3, 4, 2, 2, 1, 1, 1, 2, 2, 4]
def baseStart_2591349 : Nat := 118140960795 + 2591349 * 2 ^ 59
def prefixEnd_2591349 : Nat := 4983230072969 + 3 ^ 40 * 2591349 * 2
def baseEnd_2591349 : Nat := 1330607580547887068820109

theorem tailTrace_2591349 : CollatzResearch.WordTrace tailWord_2591349 prefixEnd_2591349 1330607580547887068820109 := by
  unfold tailWord_2591349
  simp only [CollatzResearch.WordTrace]
  refine ⟨94514262688992615019737101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63009508459328410013158067 94514262688992615019737101)
  ·
    refine ⟨35442848508372230632401413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94514262688992615019737101 35442848508372230632401413)
    ·
      refine ⟨6645534095319793243575265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35442848508372230632401413 6645534095319793243575265)
      ·
        refine ⟨4984150571489844932681449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6645534095319793243575265 4984150571489844932681449)
        ·
          refine ⟨3738112928617383699511087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4984150571489844932681449 3738112928617383699511087)
          ·
            refine ⟨5607169392926075549266631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3738112928617383699511087 5607169392926075549266631)
            ·
              refine ⟨8410754089389113323899947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5607169392926075549266631 8410754089389113323899947)
              ·
                refine ⟨12616131134083669985849921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8410754089389113323899947 12616131134083669985849921)
                ·
                  refine ⟨9462098350562752489387441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12616131134083669985849921 9462098350562752489387441)
                  ·
                    refine ⟨7096573762922064367040581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9462098350562752489387441 7096573762922064367040581)
                    ·
                      refine ⟨1330607580547887068820109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7096573762922064367040581 1330607580547887068820109)
                      ·
                        rfl

theorem cell23_2591349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_2591349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2591349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2591349 prefixEnd_2591349 := by exact prefixLift 2591349
  have htrace : WordTrace (prefixWord ++ tailWord_2591349) baseStart_2591349 baseEnd_2591349 := by
    simpa [prefixWord, tailWord_2591349, baseEnd_2591349] using wordTrace_append hprefix tailTrace_2591349
  have hstable : (prefixWord ++ tailWord_2591349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591349).length < 2 ^ (prefixWord ++ tailWord_2591349).sum := by decide
  have hdescent : baseEnd_2591349 < baseStart_2591349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591375 : List Nat := [1, 1, 2, 1, 1, 1, 1, 7, 1, 3, 4]
def baseStart_2591375 : Nat := 118140960795 + 2591375 * 2 ^ 59
def prefixEnd_2591375 : Nat := 4983230072969 + 3 ^ 40 * 2591375 * 2
def baseEnd_2591375 : Nat := 1330620931044903967094989

theorem tailTrace_2591375 : CollatzResearch.WordTrace tailWord_2591375 prefixEnd_2591375 1330620931044903967094989 := by
  unfold tailWord_2591375
  simp only [CollatzResearch.WordTrace]
  refine ⟨94515210986898421460183579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63010140657932280973455719 94515210986898421460183579)
  ·
    refine ⟨141772816480347632190275369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94515210986898421460183579 141772816480347632190275369)
    ·
      refine ⟨106329612360260724142706527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141772816480347632190275369 106329612360260724142706527)
      ·
        refine ⟨159494418540391086214059791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106329612360260724142706527 159494418540391086214059791)
        ·
          refine ⟨239241627810586629321089687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159494418540391086214059791 239241627810586629321089687)
          ·
            refine ⟨358862441715879943981634531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239241627810586629321089687 358862441715879943981634531)
            ·
              refine ⟨538293662573819915972451797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 358862441715879943981634531 538293662573819915972451797)
              ·
                refine ⟨12616257716573904280604339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 538293662573819915972451797 12616257716573904280604339)
                ·
                  refine ⟨18924386574860856420906509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12616257716573904280604339 18924386574860856420906509)
                  ·
                    refine ⟨7096644965572821157839941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18924386574860856420906509 7096644965572821157839941)
                    ·
                      refine ⟨1330620931044903967094989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7096644965572821157839941 1330620931044903967094989)
                      ·
                        rfl

theorem cell23_2591375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 3, 4].length) (baseStart_2591375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2591375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2591375 prefixEnd_2591375 := by exact prefixLift 2591375
  have htrace : WordTrace (prefixWord ++ tailWord_2591375) baseStart_2591375 baseEnd_2591375 := by
    simpa [prefixWord, tailWord_2591375, baseEnd_2591375] using wordTrace_append hprefix tailTrace_2591375
  have hstable : (prefixWord ++ tailWord_2591375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591375).length < 2 ^ (prefixWord ++ tailWord_2591375).sum := by decide
  have hdescent : baseEnd_2591375 < baseStart_2591375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591422 : List Nat := [4, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4]
def baseStart_2591422 : Nat := 118140960795 + 2591422 * 2 ^ 59
def prefixEnd_2591422 : Nat := 4983230072969 + 3 ^ 40 * 2591422 * 2
def baseEnd_2591422 : Nat := 1330645064635665283207273

theorem tailTrace_2591422 : CollatzResearch.WordTrace tailWord_2591422 prefixEnd_2591422 1330645064635665283207273 := by
  unfold tailWord_2591422
  simp only [CollatzResearch.WordTrace]
  refine ⟨11814615652216018560893065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63011283478485432324763013 11814615652216018560893065)
  ·
    refine ⟨8860961739162013920669799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11814615652216018560893065 8860961739162013920669799)
    ·
      refine ⟨13291442608743020881004699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8860961739162013920669799 13291442608743020881004699)
      ·
        refine ⟨19937163913114531321507049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13291442608743020881004699 19937163913114531321507049)
        ·
          refine ⟨14952872934835898491130287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19937163913114531321507049 14952872934835898491130287)
          ·
            refine ⟨22429309402253847736695431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14952872934835898491130287 22429309402253847736695431)
            ·
              refine ⟨33643964103380771605043147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22429309402253847736695431 33643964103380771605043147)
              ·
                refine ⟨50465946155071157407564721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33643964103380771605043147 50465946155071157407564721)
                ·
                  refine ⟨37849459616303368055673541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50465946155071157407564721 37849459616303368055673541)
                  ·
                    refine ⟨7096773678056881510438789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37849459616303368055673541 7096773678056881510438789)
                    ·
                      refine ⟨1330645064635665283207273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7096773678056881510438789 1330645064635665283207273)
                      ·
                        rfl

theorem cell23_2591422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_2591422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2591422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2591422 prefixEnd_2591422 := by exact prefixLift 2591422
  have htrace : WordTrace (prefixWord ++ tailWord_2591422) baseStart_2591422 baseEnd_2591422 := by
    simpa [prefixWord, tailWord_2591422, baseEnd_2591422] using wordTrace_append hprefix tailTrace_2591422
  have hstable : (prefixWord ++ tailWord_2591422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591422).length < 2 ^ (prefixWord ++ tailWord_2591422).sum := by decide
  have hdescent : baseEnd_2591422 < baseStart_2591422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591496 : List Nat := [2, 1, 3, 2, 2, 3, 3, 1, 1, 5]
def baseStart_2591496 : Nat := 118140960795 + 2591496 * 2 ^ 59
def prefixEnd_2591496 : Nat := 4983230072969 + 3 ^ 40 * 2591496 * 2
def baseEnd_2591496 : Nat := 443561020734699331227311

theorem tailTrace_2591496 : CollatzResearch.WordTrace tailWord_2591496 prefixEnd_2591496 443561020734699331227311 := by
  unfold tailWord_2591496
  simp only [CollatzResearch.WordTrace]
  refine ⟨47259812109730029562669171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63013082812973372750225561 47259812109730029562669171)
  ·
    refine ⟨70889718164595044344003757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47259812109730029562669171 70889718164595044344003757)
    ·
      refine ⟨26583644311723141629001409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70889718164595044344003757 26583644311723141629001409)
      ·
        refine ⟨19937733233792356221751057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26583644311723141629001409 19937733233792356221751057)
        ·
          refine ⟨14953299925344267166313293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19937733233792356221751057 14953299925344267166313293)
          ·
            refine ⟨5607487472004100187367485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14953299925344267166313293 5607487472004100187367485)
            ·
              refine ⟨2102807802001537570262807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5607487472004100187367485 2102807802001537570262807)
              ·
                refine ⟨3154211703002306355394211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2102807802001537570262807 3154211703002306355394211)
                ·
                  refine ⟨4731317554503459533091317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3154211703002306355394211 4731317554503459533091317)
                  ·
                    refine ⟨443561020734699331227311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4731317554503459533091317 443561020734699331227311)
                    ·
                      rfl

theorem cell23_2591496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 1, 1, 5].length) (baseStart_2591496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2591496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2591496 prefixEnd_2591496 := by exact prefixLift 2591496
  have htrace : WordTrace (prefixWord ++ tailWord_2591496) baseStart_2591496 baseEnd_2591496 := by
    simpa [prefixWord, tailWord_2591496, baseEnd_2591496] using wordTrace_append hprefix tailTrace_2591496
  have hstable : (prefixWord ++ tailWord_2591496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591496).length < 2 ^ (prefixWord ++ tailWord_2591496).sum := by decide
  have hdescent : baseEnd_2591496 < baseStart_2591496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591512 : List Nat := [2, 1, 2, 3, 1, 1, 1, 1, 5, 2, 4]
def baseStart_2591512 : Nat := 118140960795 + 2591512 * 2 ^ 59
def prefixEnd_2591512 : Nat := 4983230072969 + 3 ^ 40 * 2591512 * 2
def baseEnd_2591512 : Nat := 1330691277894569931081859

theorem tailTrace_2591512 : CollatzResearch.WordTrace tailWord_2591512 prefixEnd_2591512 1330691277894569931081859 := by
  unfold tailWord_2591512
  simp only [CollatzResearch.WordTrace]
  refine ⟨47260103893701046928960395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63013471858268062571947193 47260103893701046928960395)
  ·
    refine ⟨70890155840551570393440593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47260103893701046928960395 70890155840551570393440593)
    ·
      refine ⟨53167616880413677795080445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70890155840551570393440593 53167616880413677795080445)
      ·
        refine ⟨19937856330155129173155167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53167616880413677795080445 19937856330155129173155167)
        ·
          refine ⟨29906784495232693759732751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19937856330155129173155167 29906784495232693759732751)
          ·
            refine ⟨44860176742849040639599127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29906784495232693759732751 44860176742849040639599127)
            ·
              refine ⟨67290265114273560959398691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44860176742849040639599127 67290265114273560959398691)
              ·
                refine ⟨100935397671410341439098037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67290265114273560959398691 100935397671410341439098037)
                ·
                  refine ⟨9462693531694719509915441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 100935397671410341439098037 9462693531694719509915441)
                  ·
                    refine ⟨7097020148771039632436581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9462693531694719509915441 7097020148771039632436581)
                    ·
                      refine ⟨1330691277894569931081859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7097020148771039632436581 1330691277894569931081859)
                      ·
                        rfl

theorem cell23_2591512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_2591512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2591512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2591512 prefixEnd_2591512 := by exact prefixLift 2591512
  have htrace : WordTrace (prefixWord ++ tailWord_2591512) baseStart_2591512 baseEnd_2591512 := by
    simpa [prefixWord, tailWord_2591512, baseEnd_2591512] using wordTrace_append hprefix tailTrace_2591512
  have hstable : (prefixWord ++ tailWord_2591512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591512).length < 2 ^ (prefixWord ++ tailWord_2591512).sum := by decide
  have hdescent : baseEnd_2591512 < baseStart_2591512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591519 : List Nat := [1, 1, 2, 4, 2, 2, 1, 2, 3, 2, 3]
def baseStart_2591519 : Nat := 118140960795 + 2591519 * 2 ^ 59
def prefixEnd_2591519 : Nat := 4983230072969 + 3 ^ 40 * 2591519 * 2
def baseEnd_2591519 : Nat := 1330694872259151403694327

theorem tailTrace_2591519 : CollatzResearch.WordTrace tailWord_2591519 prefixEnd_2591519 1330694872259151403694327 := by
  unfold tailWord_2591519
  simp only [CollatzResearch.WordTrace]
  refine ⟨94520463098376734053425611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63013642065584489368950407 94520463098376734053425611)
  ·
    refine ⟨141780694647565101080138417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94520463098376734053425611 141780694647565101080138417)
    ·
      refine ⟨106335520985673825810103813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141780694647565101080138417 106335520985673825810103813)
      ·
        refine ⟨19937910184813842339394465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106335520985673825810103813 19937910184813842339394465)
        ·
          refine ⟨14953432638610381754545849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19937910184813842339394465 14953432638610381754545849)
          ·
            refine ⟨11215074478957786315909387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14953432638610381754545849 11215074478957786315909387)
            ·
              refine ⟨16822611718436679473864081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11215074478957786315909387 16822611718436679473864081)
              ·
                refine ⟨12616958788827509605398061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16822611718436679473864081 12616958788827509605398061)
                ·
                  refine ⟨4731359545810316102024273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12616958788827509605398061 4731359545810316102024273)
                  ·
                    refine ⟨3548519659357737076518205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4731359545810316102024273 3548519659357737076518205)
                    ·
                      refine ⟨1330694872259151403694327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3548519659357737076518205 1330694872259151403694327)
                      ·
                        rfl

theorem cell23_2591519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_2591519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2591519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2591519 prefixEnd_2591519 := by exact prefixLift 2591519
  have htrace : WordTrace (prefixWord ++ tailWord_2591519) baseStart_2591519 baseEnd_2591519 := by
    simpa [prefixWord, tailWord_2591519, baseEnd_2591519] using wordTrace_append hprefix tailTrace_2591519
  have hstable : (prefixWord ++ tailWord_2591519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591519).length < 2 ^ (prefixWord ++ tailWord_2591519).sum := by decide
  have hdescent : baseEnd_2591519 < baseStart_2591519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591539 : List Nat := [1, 1, 1, 2, 6, 2, 3, 7]
def baseStart_2591539 : Nat := 118140960795 + 2591539 * 2 ^ 59
def prefixEnd_2591539 : Nat := 4983230072969 + 3 ^ 40 * 2591539 * 2
def baseEnd_2591539 : Nat := 49285375624897826868305

theorem tailTrace_2591539 : CollatzResearch.WordTrace tailWord_2591539 prefixEnd_2591539 49285375624897826868305 := by
  unfold tailWord_2591539
  simp only [CollatzResearch.WordTrace]
  refine ⟨94521192558304277469153671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63014128372202851646102447 94521192558304277469153671)
  ·
    refine ⟨141781788837456416203730507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94521192558304277469153671 141781788837456416203730507)
    ·
      refine ⟨212672683256184624305595761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141781788837456416203730507 212672683256184624305595761)
      ·
        refine ⟨159504512442138468229196821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212672683256184624305595761 159504512442138468229196821)
        ·
          refine ⟨7476774020725240698243601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 159504512442138468229196821 7476774020725240698243601)
          ·
            refine ⟨5607580515543930523682701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7476774020725240698243601 5607580515543930523682701)
            ·
              refine ⟨2102842693328973946381013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5607580515543930523682701 2102842693328973946381013)
              ·
                refine ⟨49285375624897826868305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2102842693328973946381013 49285375624897826868305)
                ·
                  rfl

theorem cell23_2591539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 7].length) (baseStart_2591539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2591539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2591539 prefixEnd_2591539 := by exact prefixLift 2591539
  have htrace : WordTrace (prefixWord ++ tailWord_2591539) baseStart_2591539 baseEnd_2591539 := by
    simpa [prefixWord, tailWord_2591539, baseEnd_2591539] using wordTrace_append hprefix tailTrace_2591539
  have hstable : (prefixWord ++ tailWord_2591539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591539).length < 2 ^ (prefixWord ++ tailWord_2591539).sum := by decide
  have hdescent : baseEnd_2591539 < baseStart_2591539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591550 : List Nat := [4, 2, 1, 2, 3, 2, 2, 1, 1, 1, 4]
def baseStart_2591550 : Nat := 118140960795 + 2591550 * 2 ^ 59
def prefixEnd_2591550 : Nat := 4983230072969 + 3 ^ 40 * 2591550 * 2
def baseEnd_2591550 : Nat := 1330710790159440782406685

theorem tailTrace_2591550 : CollatzResearch.WordTrace tailWord_2591550 prefixEnd_2591550 1330710790159440782406685 := by
  unfold tailWord_2591550
  simp only [CollatzResearch.WordTrace]
  refine ⟨11815199220158053293475513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63014395840842950898536069 11815199220158053293475513)
  ·
    refine ⟨8861399415118539970106635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11815199220158053293475513 8861399415118539970106635)
    ·
      refine ⟨13292099122677809955159953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8861399415118539970106635 13292099122677809955159953)
      ·
        refine ⟨9969074342008357466369965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13292099122677809955159953 9969074342008357466369965)
        ·
          refine ⟨3738402878253134049888737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9969074342008357466369965 3738402878253134049888737)
          ·
            refine ⟨2803802158689850537416553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3738402878253134049888737 2803802158689850537416553)
            ·
              refine ⟨2102851619017387903062415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2803802158689850537416553 2102851619017387903062415)
              ·
                refine ⟨3154277428526081854593623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2102851619017387903062415 3154277428526081854593623)
                ·
                  refine ⟨4731416142789122781890435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3154277428526081854593623 4731416142789122781890435)
                  ·
                    refine ⟨7097124214183684172835653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4731416142789122781890435 7097124214183684172835653)
                    ·
                      refine ⟨1330710790159440782406685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7097124214183684172835653 1330710790159440782406685)
                      ·
                        rfl

theorem cell23_2591550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_2591550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2591550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2591550 prefixEnd_2591550 := by exact prefixLift 2591550
  have htrace : WordTrace (prefixWord ++ tailWord_2591550) baseStart_2591550 baseEnd_2591550 := by
    simpa [prefixWord, tailWord_2591550, baseEnd_2591550] using wordTrace_append hprefix tailTrace_2591550
  have hstable : (prefixWord ++ tailWord_2591550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591550).length < 2 ^ (prefixWord ++ tailWord_2591550).sum := by decide
  have hdescent : baseEnd_2591550 < baseStart_2591550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591556 : List Nat := [2, 3, 4, 2, 1, 1, 10]
def baseStart_2591556 : Nat := 118140960795 + 2591556 * 2 ^ 59
def prefixEnd_2591556 : Nat := 4983230072969 + 3 ^ 40 * 2591556 * 2
def baseEnd_2591556 : Nat := 16428566309177379739897

theorem tailTrace_2591556 : CollatzResearch.WordTrace tailWord_2591556 prefixEnd_2591556 16428566309177379739897 := by
  unfold tailWord_2591556
  simp only [CollatzResearch.WordTrace]
  refine ⟨47260906299621344686261261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63014541732828459581681681 47260906299621344686261261)
  ·
    refine ⟨17722839862358004257347973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47260906299621344686261261 17722839862358004257347973)
    ·
      refine ⟨3323032474192125798252745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17722839862358004257347973 3323032474192125798252745)
      ·
        refine ⟨2492274355644094348689559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3323032474192125798252745 2492274355644094348689559)
        ·
          refine ⟨3738411533466141523034339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2492274355644094348689559 3738411533466141523034339)
          ·
            refine ⟨5607617300199212284551509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3738411533466141523034339 5607617300199212284551509)
            ·
              refine ⟨16428566309177379739897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5607617300199212284551509 16428566309177379739897)
              ·
                rfl

theorem cell23_2591556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 10].length) (baseStart_2591556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2591556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2591556 prefixEnd_2591556 := by exact prefixLift 2591556
  have htrace : WordTrace (prefixWord ++ tailWord_2591556) baseStart_2591556 baseEnd_2591556 := by
    simpa [prefixWord, tailWord_2591556, baseEnd_2591556] using wordTrace_append hprefix tailTrace_2591556
  have hstable : (prefixWord ++ tailWord_2591556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591556).length < 2 ^ (prefixWord ++ tailWord_2591556).sum := by decide
  have hdescent : baseEnd_2591556 < baseStart_2591556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591562 : List Nat := [3, 1, 2, 1, 1, 1, 2, 1, 4, 2, 5]
def baseStart_2591562 : Nat := 118140960795 + 2591562 * 2 ^ 59
def prefixEnd_2591562 : Nat := 4983230072969 + 3 ^ 40 * 2591562 * 2
def baseEnd_2591562 : Nat := 1330716951927294735456629

theorem tailTrace_2591562 : CollatzResearch.WordTrace tailWord_2591562 prefixEnd_2591562 1330716951927294735456629 := by
  unfold tailWord_2591562
  simp only [CollatzResearch.WordTrace]
  refine ⟨23630507859305238099310235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63014687624813968264827293 23630507859305238099310235)
  ·
    refine ⟨35445761788957857148965353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23630507859305238099310235 35445761788957857148965353)
    ·
      refine ⟨26584321341718392861724015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35445761788957857148965353 26584321341718392861724015)
      ·
        refine ⟨39876482012577589292586023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26584321341718392861724015 39876482012577589292586023)
        ·
          refine ⟨59814723018866383938879035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39876482012577589292586023 59814723018866383938879035)
          ·
            refine ⟨89722084528299575908318553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59814723018866383938879035 89722084528299575908318553)
            ·
              refine ⟨67291563396224681931238915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89722084528299575908318553 67291563396224681931238915)
              ·
                refine ⟨100937345094337022896858373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67291563396224681931238915 100937345094337022896858373)
                ·
                  refine ⟨18925752205188191793160945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 100937345094337022896858373 18925752205188191793160945)
                  ·
                    refine ⟨14194314153891143844870709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18925752205188191793160945 14194314153891143844870709)
                    ·
                      refine ⟨1330716951927294735456629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14194314153891143844870709 1330716951927294735456629)
                      ·
                        rfl

theorem cell23_2591562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_2591562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2591562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2591562 prefixEnd_2591562 := by exact prefixLift 2591562
  have htrace : WordTrace (prefixWord ++ tailWord_2591562) baseStart_2591562 baseEnd_2591562 := by
    simpa [prefixWord, tailWord_2591562, baseEnd_2591562] using wordTrace_append hprefix tailTrace_2591562
  have hstable : (prefixWord ++ tailWord_2591562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591562).length < 2 ^ (prefixWord ++ tailWord_2591562).sum := by decide
  have hdescent : baseEnd_2591562 < baseStart_2591562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591583 : List Nat := [1, 1, 2, 3, 1, 3, 5, 1, 2, 1, 3]
def baseStart_2591583 : Nat := 118140960795 + 2591583 * 2 ^ 59
def prefixEnd_2591583 : Nat := 4983230072969 + 3 ^ 40 * 2591583 * 2
def baseEnd_2591583 : Nat := 1330727735021039153294033

theorem tailTrace_2591583 : CollatzResearch.WordTrace tailWord_2591583 prefixEnd_2591583 1330727735021039153294033 := by
  unfold tailWord_2591583
  simp only [CollatzResearch.WordTrace]
  refine ⟨94522797370144872983755403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63015198246763248655836935 94522797370144872983755403)
  ·
    refine ⟨141784196055217309475633105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94522797370144872983755403 141784196055217309475633105)
    ·
      refine ⟨106338147041412982106724829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141784196055217309475633105 106338147041412982106724829)
      ·
        refine ⟨39876805140529868290021811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106338147041412982106724829 39876805140529868290021811)
        ·
          refine ⟨59815207710794802435032717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39876805140529868290021811 59815207710794802435032717)
          ·
            refine ⟨22430702891548050913137269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59815207710794802435032717 22430702891548050913137269)
            ·
              refine ⟨2102878396082629773106619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22430702891548050913137269 2102878396082629773106619)
              ·
                refine ⟨3154317594123944659659929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2102878396082629773106619 3154317594123944659659929)
                ·
                  refine ⟨2365738195592958494744947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3154317594123944659659929 2365738195592958494744947)
                  ·
                    refine ⟨3548607293389437742117421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2365738195592958494744947 3548607293389437742117421)
                    ·
                      refine ⟨1330727735021039153294033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3548607293389437742117421 1330727735021039153294033)
                      ·
                        rfl

theorem cell23_2591583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 1, 2, 1, 3].length) (baseStart_2591583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2591583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2591583 prefixEnd_2591583 := by exact prefixLift 2591583
  have htrace : WordTrace (prefixWord ++ tailWord_2591583) baseStart_2591583 baseEnd_2591583 := by
    simpa [prefixWord, tailWord_2591583, baseEnd_2591583] using wordTrace_append hprefix tailTrace_2591583
  have hstable : (prefixWord ++ tailWord_2591583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591583).length < 2 ^ (prefixWord ++ tailWord_2591583).sum := by decide
  have hdescent : baseEnd_2591583 < baseStart_2591583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591609 : List Nat := [1, 2, 1, 3, 2, 4, 1, 1, 2, 1, 5]
def baseStart_2591609 : Nat := 118140960795 + 2591609 * 2 ^ 59
def prefixEnd_2591609 : Nat := 4983230072969 + 3 ^ 40 * 2591609 * 2
def baseEnd_2591609 : Nat := 1330741085518056051568913

theorem tailTrace_2591609 : CollatzResearch.WordTrace tailWord_2591609 prefixEnd_2591609 1330741085518056051568913 := by
  unfold tailWord_2591609
  simp only [CollatzResearch.WordTrace]
  refine ⟨94523745668050679424201881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63015830445367119616134587 94523745668050679424201881)
  ·
    refine ⟨70892809251038009568151411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94523745668050679424201881 70892809251038009568151411)
    ·
      refine ⟨106339213876557014352227117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70892809251038009568151411 106339213876557014352227117)
      ·
        refine ⟨39877205203708880382085169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106339213876557014352227117 39877205203708880382085169)
        ·
          refine ⟨29907903902781660286563877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39877205203708880382085169 29907903902781660286563877)
          ·
            refine ⟨5607731981771561303730727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29907903902781660286563877 5607731981771561303730727)
            ·
              refine ⟨8411597972657341955596091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5607731981771561303730727 8411597972657341955596091)
              ·
                refine ⟨12617396958986012933394137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8411597972657341955596091 12617396958986012933394137)
                ·
                  refine ⟨9463047719239509700045603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12617396958986012933394137 9463047719239509700045603)
                  ·
                    refine ⟨14194571578859264550068405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9463047719239509700045603 14194571578859264550068405)
                    ·
                      refine ⟨1330741085518056051568913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14194571578859264550068405 1330741085518056051568913)
                      ·
                        rfl

theorem cell23_2591609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 2, 1, 5].length) (baseStart_2591609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2591609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2591609 prefixEnd_2591609 := by exact prefixLift 2591609
  have htrace : WordTrace (prefixWord ++ tailWord_2591609) baseStart_2591609 baseEnd_2591609 := by
    simpa [prefixWord, tailWord_2591609, baseEnd_2591609] using wordTrace_append hprefix tailTrace_2591609
  have hstable : (prefixWord ++ tailWord_2591609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591609).length < 2 ^ (prefixWord ++ tailWord_2591609).sum := by decide
  have hdescent : baseEnd_2591609 < baseStart_2591609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591612 : List Nat := [2, 2, 2, 1, 1, 1, 1, 4, 9]
def baseStart_2591612 : Nat := 118140960795 + 2591612 * 2 ^ 59
def prefixEnd_2591612 : Nat := 4983230072969 + 3 ^ 40 * 2591612 * 2
def baseEnd_2591612 : Nat := 147860291773335504425711

theorem tailTrace_2591612 : CollatzResearch.WordTrace tailWord_2591612 prefixEnd_2591612 147860291773335504425711 := by
  unfold tailWord_2591612
  simp only [CollatzResearch.WordTrace]
  refine ⟨47261927543519905468280545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63015903391359873957707393 47261927543519905468280545)
  ·
    refine ⟨35446445657639929101210409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47261927543519905468280545 35446445657639929101210409)
    ·
      refine ⟨26584834243229946825907807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35446445657639929101210409 26584834243229946825907807)
      ·
        refine ⟨39877251364844920238861711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26584834243229946825907807 39877251364844920238861711)
        ·
          refine ⟨59815877047267380358292567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39877251364844920238861711 59815877047267380358292567)
          ·
            refine ⟨89723815570901070537438851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59815877047267380358292567 89723815570901070537438851)
            ·
              refine ⟨134585723356351605806158277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89723815570901070537438851 134585723356351605806158277)
              ·
                refine ⟨25234823129315926088654677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 134585723356351605806158277 25234823129315926088654677)
                ·
                  refine ⟨147860291773335504425711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 25234823129315926088654677 147860291773335504425711)
                  ·
                    rfl

theorem cell23_2591612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 9].length) (baseStart_2591612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2591612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2591612 prefixEnd_2591612 := by exact prefixLift 2591612
  have htrace : WordTrace (prefixWord ++ tailWord_2591612) baseStart_2591612 baseEnd_2591612 := by
    simpa [prefixWord, tailWord_2591612, baseEnd_2591612] using wordTrace_append hprefix tailTrace_2591612
  have hstable : (prefixWord ++ tailWord_2591612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591612).length < 2 ^ (prefixWord ++ tailWord_2591612).sum := by decide
  have hdescent : baseEnd_2591612 < baseStart_2591612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591623 : List Nat := [1, 1, 4, 2, 3, 1, 2, 1, 4, 2, 2]
def baseStart_2591623 : Nat := 118140960795 + 2591623 * 2 ^ 59
def prefixEnd_2591623 : Nat := 4983230072969 + 3 ^ 40 * 2591623 * 2
def baseEnd_2591623 : Nat := 1330748274247218996793849

theorem tailTrace_2591623 : CollatzResearch.WordTrace tailWord_2591623 prefixEnd_2591623 1330748274247218996793849 := by
  unfold tailWord_2591623
  simp only [CollatzResearch.WordTrace]
  refine ⟨94524256289999959815211523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63016170859999973210141015 94524256289999959815211523)
  ·
    refine ⟨141786384434999939722817285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94524256289999959815211523 141786384434999939722817285)
    ·
      refine ⟨26584947081562488698028241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141786384434999939722817285 26584947081562488698028241)
      ·
        refine ⟨19938710311171866523521181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26584947081562488698028241 19938710311171866523521181)
        ·
          refine ⟨7477016366689449946320443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19938710311171866523521181 7477016366689449946320443)
          ·
            refine ⟨11215524550034174919480665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7477016366689449946320443 11215524550034174919480665)
            ·
              refine ⟨8411643412525631189610499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11215524550034174919480665 8411643412525631189610499)
              ·
                refine ⟨12617465118788446784415749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8411643412525631189610499 12617465118788446784415749)
                ·
                  refine ⟨2365774709772833772077953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12617465118788446784415749 2365774709772833772077953)
                  ·
                    refine ⟨1774331032329625329058465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2365774709772833772077953 1774331032329625329058465)
                    ·
                      refine ⟨1330748274247218996793849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1774331032329625329058465 1330748274247218996793849)
                      ·
                        rfl

theorem cell23_2591623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 4, 2, 2].length) (baseStart_2591623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2591623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2591623 prefixEnd_2591623 := by exact prefixLift 2591623
  have htrace : WordTrace (prefixWord ++ tailWord_2591623) baseStart_2591623 baseEnd_2591623 := by
    simpa [prefixWord, tailWord_2591623, baseEnd_2591623] using wordTrace_append hprefix tailTrace_2591623
  have hstable : (prefixWord ++ tailWord_2591623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591623).length < 2 ^ (prefixWord ++ tailWord_2591623).sum := by decide
  have hdescent : baseEnd_2591623 < baseStart_2591623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591634 : List Nat := [3, 2, 3, 2, 3, 1, 2, 1, 2, 1, 3]
def baseStart_2591634 : Nat := 118140960795 + 2591634 * 2 ^ 59
def prefixEnd_2591634 : Nat := 4983230072969 + 3 ^ 40 * 2591634 * 2
def baseEnd_2591634 : Nat := 1330753922534418453756299

theorem tailTrace_2591634 : CollatzResearch.WordTrace tailWord_2591634 prefixEnd_2591634 1330753922534418453756299 := by
  unfold tailWord_2591634
  simp only [CollatzResearch.WordTrace]
  refine ⟨23631164373240027173465489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63016438328640072462574637 23631164373240027173465489)
  ·
    refine ⟨17723373279930020380099117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23631164373240027173465489 17723373279930020380099117)
    ·
      refine ⟨6646264979973757642537169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17723373279930020380099117 6646264979973757642537169)
      ·
        refine ⟨4984698734980318231902877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6646264979973757642537169 4984698734980318231902877)
        ·
          refine ⟨1869262025617619336963579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4984698734980318231902877 1869262025617619336963579)
          ·
            refine ⟨2803893038426429005445369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1869262025617619336963579 2803893038426429005445369)
            ·
              refine ⟨2102919778819821754084027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2803893038426429005445369 2102919778819821754084027)
              ·
                refine ⟨3154379668229732631126041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2102919778819821754084027 3154379668229732631126041)
                ·
                  refine ⟨2365784751172299473344531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3154379668229732631126041 2365784751172299473344531)
                  ·
                    refine ⟨3548677126758449210016797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2365784751172299473344531 3548677126758449210016797)
                    ·
                      refine ⟨1330753922534418453756299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3548677126758449210016797 1330753922534418453756299)
                      ·
                        rfl

theorem cell23_2591634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_2591634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2591634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2591634 prefixEnd_2591634 := by exact prefixLift 2591634
  have htrace : WordTrace (prefixWord ++ tailWord_2591634) baseStart_2591634 baseEnd_2591634 := by
    simpa [prefixWord, tailWord_2591634, baseEnd_2591634] using wordTrace_append hprefix tailTrace_2591634
  have hstable : (prefixWord ++ tailWord_2591634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591634).length < 2 ^ (prefixWord ++ tailWord_2591634).sum := by decide
  have hdescent : baseEnd_2591634 < baseStart_2591634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591639 : List Nat := [1, 1, 3, 3, 1, 2, 2, 1, 1, 5, 3]
def baseStart_2591639 : Nat := 118140960795 + 2591639 * 2 ^ 59
def prefixEnd_2591639 : Nat := 4983230072969 + 3 ^ 40 * 2591639 * 2
def baseEnd_2591639 : Nat := 1330756489937690934193775

theorem tailTrace_2591639 : CollatzResearch.WordTrace tailWord_2591639 prefixEnd_2591639 1330756489937690934193775 := by
  unfold tailWord_2591639
  simp only [CollatzResearch.WordTrace]
  refine ⟨94524839857941994547793971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63016559905294663031862647 94524839857941994547793971)
  ·
    refine ⟨141787259786912991821690957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94524839857941994547793971 141787259786912991821690957)
    ·
      refine ⟨53170222420092371933134109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141787259786912991821690957 53170222420092371933134109)
      ·
        refine ⟨19938833407534639474925291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53170222420092371933134109 19938833407534639474925291)
        ·
          refine ⟨29908250111301959212387937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19938833407534639474925291 29908250111301959212387937)
          ·
            refine ⟨22431187583476469409290953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29908250111301959212387937 22431187583476469409290953)
            ·
              refine ⟨16823390687607352056968215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22431187583476469409290953 16823390687607352056968215)
              ·
                refine ⟨25235086031411028085452323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16823390687607352056968215 25235086031411028085452323)
                ·
                  refine ⟨37852629047116542128178485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25235086031411028085452323 37852629047116542128178485)
                  ·
                    refine ⟨3548683973167175824516733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37852629047116542128178485 3548683973167175824516733)
                    ·
                      refine ⟨1330756489937690934193775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3548683973167175824516733 1330756489937690934193775)
                      ·
                        rfl

theorem cell23_2591639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_2591639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2591639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2591639 prefixEnd_2591639 := by exact prefixLift 2591639
  have htrace : WordTrace (prefixWord ++ tailWord_2591639) baseStart_2591639 baseEnd_2591639 := by
    simpa [prefixWord, tailWord_2591639, baseEnd_2591639] using wordTrace_append hprefix tailTrace_2591639
  have hstable : (prefixWord ++ tailWord_2591639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591639).length < 2 ^ (prefixWord ++ tailWord_2591639).sum := by decide
  have hdescent : baseEnd_2591639 < baseStart_2591639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591669 : List Nat := [1, 3, 3, 2, 1, 1, 1, 1, 3, 2, 5]
def baseStart_2591669 : Nat := 118140960795 + 2591669 * 2 ^ 59
def prefixEnd_2591669 : Nat := 4983230072969 + 3 ^ 40 * 2591669 * 2
def baseEnd_2591669 : Nat := 1330771894357325816818637

theorem tailTrace_2591669 : CollatzResearch.WordTrace tailWord_2591669 prefixEnd_2591669 1330771894357325816818637 := by
  unfold tailWord_2591669
  simp only [CollatzResearch.WordTrace]
  refine ⟨94525934047833309671386061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63017289365222206447590707 94525934047833309671386061)
  ·
    refine ⟨35447225267937491126769773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94525934047833309671386061 35447225267937491126769773)
    ·
      refine ⟨13292709475476559172538665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35447225267937491126769773 13292709475476559172538665)
      ·
        refine ⟨9969532106607419379403999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13292709475476559172538665 9969532106607419379403999)
        ·
          refine ⟨14954298159911129069105999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9969532106607419379403999 14954298159911129069105999)
          ·
            refine ⟨22431447239866693603658999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14954298159911129069105999 22431447239866693603658999)
            ·
              refine ⟨33647170859800040405488499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22431447239866693603658999 33647170859800040405488499)
              ·
                refine ⟨50470756289700060608232749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33647170859800040405488499 50470756289700060608232749)
                ·
                  refine ⟨18926533608637522728087281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50470756289700060608232749 18926533608637522728087281)
                  ·
                    refine ⟨14194900206478142046065461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18926533608637522728087281 14194900206478142046065461)
                    ·
                      refine ⟨1330771894357325816818637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14194900206478142046065461 1330771894357325816818637)
                      ·
                        rfl

theorem cell23_2591669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_2591669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2591669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2591669 prefixEnd_2591669 := by exact prefixLift 2591669
  have htrace : WordTrace (prefixWord ++ tailWord_2591669) baseStart_2591669 baseEnd_2591669 := by
    simpa [prefixWord, tailWord_2591669, baseEnd_2591669] using wordTrace_append hprefix tailTrace_2591669
  have hstable : (prefixWord ++ tailWord_2591669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591669).length < 2 ^ (prefixWord ++ tailWord_2591669).sum := by decide
  have hdescent : baseEnd_2591669 < baseStart_2591669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591679 : List Nat := [1, 1, 2, 2, 2, 1, 2, 3, 4, 1, 4]
def baseStart_2591679 : Nat := 118140960795 + 2591679 * 2 ^ 59
def prefixEnd_2591679 : Nat := 4983230072969 + 3 ^ 40 * 2591679 * 2
def baseEnd_2591679 : Nat := 1330777029163870777693591

theorem tailTrace_2591679 : CollatzResearch.WordTrace tailWord_2591679 prefixEnd_2591679 1330777029163870777693591 := by
  unfold tailWord_2591679
  simp only [CollatzResearch.WordTrace]
  refine ⟨94526298777797081379250091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63017532518531387586166727 94526298777797081379250091)
  ·
    refine ⟨141789448166695622068875137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94526298777797081379250091 141789448166695622068875137)
    ·
      refine ⟨106342086125021716551656353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141789448166695622068875137 106342086125021716551656353)
      ·
        refine ⟨79756564593766287413742265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106342086125021716551656353 79756564593766287413742265)
        ·
          refine ⟨59817423445324715560306699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79756564593766287413742265 59817423445324715560306699)
          ·
            refine ⟨89726135167987073340460049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59817423445324715560306699 89726135167987073340460049)
            ·
              refine ⟨67294601375990305005345037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89726135167987073340460049 67294601375990305005345037)
              ·
                refine ⟨25235475515996364377004389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67294601375990305005345037 25235475515996364377004389)
                ·
                  refine ⟨4731651659249318320688323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25235475515996364377004389 4731651659249318320688323)
                  ·
                    refine ⟨7097477488873977481032485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4731651659249318320688323 7097477488873977481032485)
                    ·
                      refine ⟨1330777029163870777693591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7097477488873977481032485 1330777029163870777693591)
                      ·
                        rfl

theorem cell23_2591679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 4, 1, 4].length) (baseStart_2591679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2591679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2591679 prefixEnd_2591679 := by exact prefixLift 2591679
  have htrace : WordTrace (prefixWord ++ tailWord_2591679) baseStart_2591679 baseEnd_2591679 := by
    simpa [prefixWord, tailWord_2591679, baseEnd_2591679] using wordTrace_append hprefix tailTrace_2591679
  have hstable : (prefixWord ++ tailWord_2591679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591679).length < 2 ^ (prefixWord ++ tailWord_2591679).sum := by decide
  have hdescent : baseEnd_2591679 < baseStart_2591679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591706 : List Nat := [3, 1, 1, 2, 4, 1, 1, 1, 5, 4]
def baseStart_2591706 : Nat := 118140960795 + 2591706 * 2 ^ 59
def prefixEnd_2591706 : Nat := 4983230072969 + 3 ^ 40 * 2591706 * 2
def baseEnd_2591706 : Nat := 443596964380514057351989

theorem tailTrace_2591706 : CollatzResearch.WordTrace tailWord_2591706 prefixEnd_2591706 443596964380514057351989 := by
  unfold tailWord_2591706
  simp only [CollatzResearch.WordTrace]
  refine ⟨23631820887174816247620743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63018189032466176660321981 23631820887174816247620743)
  ·
    refine ⟨35447731330762224371431115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23631820887174816247620743 35447731330762224371431115)
    ·
      refine ⟨53171596996143336557146673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35447731330762224371431115 53171596996143336557146673)
      ·
        refine ⟨39878697747107502417860005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53171596996143336557146673 39878697747107502417860005)
        ·
          refine ⟨7477255827582656703348751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39878697747107502417860005 7477255827582656703348751)
          ·
            refine ⟨11215883741373985055023127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7477255827582656703348751 11215883741373985055023127)
            ·
              refine ⟨16823825612060977582534691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11215883741373985055023127 16823825612060977582534691)
              ·
                refine ⟨25235738418091466373802037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16823825612060977582534691 25235738418091466373802037)
                ·
                  refine ⟨2365850476696074972543941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25235738418091466373802037 2365850476696074972543941)
                  ·
                    refine ⟨443596964380514057351989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2365850476696074972543941 443596964380514057351989)
                    ·
                      rfl

theorem cell23_2591706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 5, 4].length) (baseStart_2591706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2591706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2591706 prefixEnd_2591706 := by exact prefixLift 2591706
  have htrace : WordTrace (prefixWord ++ tailWord_2591706) baseStart_2591706 baseEnd_2591706 := by
    simpa [prefixWord, tailWord_2591706, baseEnd_2591706] using wordTrace_append hprefix tailTrace_2591706
  have hstable : (prefixWord ++ tailWord_2591706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591706).length < 2 ^ (prefixWord ++ tailWord_2591706).sum := by decide
  have hdescent : baseEnd_2591706 < baseStart_2591706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591716 : List Nat := [2, 3, 1, 1, 1, 1, 2, 5, 2, 2, 3]
def baseStart_2591716 : Nat := 118140960795 + 2591716 * 2 ^ 59
def prefixEnd_2591716 : Nat := 4983230072969 + 3 ^ 40 * 2591716 * 2
def baseEnd_2591716 : Nat := 1330796027948087132930921

theorem tailTrace_2591716 : CollatzResearch.WordTrace tailWord_2591716 prefixEnd_2591716 1330796027948087132930921 := by
  unfold tailWord_2591716
  simp only [CollatzResearch.WordTrace]
  refine ⟨47263824139331518349173501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63018432185775357798898001 47263824139331518349173501)
  ·
    refine ⟨17723934052249319380940063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47263824139331518349173501 17723934052249319380940063)
    ·
      refine ⟨26585901078373979071410095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17723934052249319380940063 26585901078373979071410095)
      ·
        refine ⟨39878851617560968607115143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26585901078373979071410095 39878851617560968607115143)
        ·
          refine ⟨59818277426341452910672715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39878851617560968607115143 59818277426341452910672715)
          ·
            refine ⟨89727416139512179366009073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59818277426341452910672715 89727416139512179366009073)
            ·
              refine ⟨67295562104634134524506805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89727416139512179366009073 67295562104634134524506805)
              ·
                refine ⟨6308958947309450111672513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67295562104634134524506805 6308958947309450111672513)
                ·
                  refine ⟨4731719210482087583754385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6308958947309450111672513 4731719210482087583754385)
                  ·
                    refine ⟨3548789407861565687815789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4731719210482087583754385 3548789407861565687815789)
                    ·
                      refine ⟨1330796027948087132930921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3548789407861565687815789 1330796027948087132930921)
                      ·
                        rfl

theorem cell23_2591716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5, 2, 2, 3].length) (baseStart_2591716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2591716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2591716 prefixEnd_2591716 := by exact prefixLift 2591716
  have htrace : WordTrace (prefixWord ++ tailWord_2591716) baseStart_2591716 baseEnd_2591716 := by
    simpa [prefixWord, tailWord_2591716, baseEnd_2591716] using wordTrace_append hprefix tailTrace_2591716
  have hstable : (prefixWord ++ tailWord_2591716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591716).length < 2 ^ (prefixWord ++ tailWord_2591716).sum := by decide
  have hdescent : baseEnd_2591716 < baseStart_2591716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591790 : List Nat := [4, 1, 3, 1, 1, 1, 3, 2, 2, 3, 2]
def baseStart_2591790 : Nat := 118140960795 + 2591790 * 2 ^ 59
def prefixEnd_2591790 : Nat := 4983230072969 + 3 ^ 40 * 2591790 * 2
def baseEnd_2591790 : Nat := 1330834025516519843405581

theorem tailTrace_2591790 : CollatzResearch.WordTrace tailWord_2591790 prefixEnd_2591790 1330834025516519843405581 := by
  unfold tailWord_2591790
  simp only [CollatzResearch.WordTrace]
  refine ⟨11816293410049368417067603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63020231520263298224360549 11816293410049368417067603)
  ·
    refine ⟨17724440115074052625601405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11816293410049368417067603 17724440115074052625601405)
    ·
      refine ⟨6646665043152769734600527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17724440115074052625601405 6646665043152769734600527)
      ·
        refine ⟨9969997564729154601900791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6646665043152769734600527 9969997564729154601900791)
        ·
          refine ⟨14954996347093731902851187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9969997564729154601900791 14954996347093731902851187)
          ·
            refine ⟨22432494520640597854276781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14954996347093731902851187 22432494520640597854276781)
            ·
              refine ⟨8412185445240224195353793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22432494520640597854276781 8412185445240224195353793)
              ·
                refine ⟨6309139083930168146515345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8412185445240224195353793 6309139083930168146515345)
                ·
                  refine ⟨4731854312947626109886509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6309139083930168146515345 4731854312947626109886509)
                  ·
                    refine ⟨1774445367355359791207441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4731854312947626109886509 1774445367355359791207441)
                    ·
                      refine ⟨1330834025516519843405581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1774445367355359791207441 1330834025516519843405581)
                      ·
                        rfl

theorem cell23_2591790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_2591790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2591790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2591790 prefixEnd_2591790 := by exact prefixLift 2591790
  have htrace : WordTrace (prefixWord ++ tailWord_2591790) baseStart_2591790 baseEnd_2591790 := by
    simpa [prefixWord, tailWord_2591790, baseEnd_2591790] using wordTrace_append hprefix tailTrace_2591790
  have hstable : (prefixWord ++ tailWord_2591790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591790).length < 2 ^ (prefixWord ++ tailWord_2591790).sum := by decide
  have hdescent : baseEnd_2591790 < baseStart_2591790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591816 : List Nat := [2, 1, 3, 1, 1, 1, 4, 3, 1, 2, 4]
def baseStart_2591816 : Nat := 118140960795 + 2591816 * 2 ^ 59
def prefixEnd_2591816 : Nat := 4983230072969 + 3 ^ 40 * 2591816 * 2
def baseEnd_2591816 : Nat := 1330847376013536741680461

theorem tailTrace_2591816 : CollatzResearch.WordTrace tailWord_2591816 prefixEnd_2591816 1330847376013536741680461 := by
  unfold tailWord_2591816
  simp only [CollatzResearch.WordTrace]
  refine ⟨47265647789150376888493651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63020863718867169184658201 47265647789150376888493651)
  ·
    refine ⟨70898471683725565332740477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47265647789150376888493651 70898471683725565332740477)
    ·
      refine ⟨26586926881397086999777679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70898471683725565332740477 26586926881397086999777679)
      ·
        refine ⟨39880390322095630499666519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26586926881397086999777679 39880390322095630499666519)
        ·
          refine ⟨59820585483143445749499779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39880390322095630499666519 59820585483143445749499779)
          ·
            refine ⟨89730878224715168624249669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59820585483143445749499779 89730878224715168624249669)
            ·
              refine ⟨16824539667134094117046813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89730878224715168624249669 16824539667134094117046813)
              ·
                refine ⟨6309202375175285293892555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16824539667134094117046813 6309202375175285293892555)
                ·
                  refine ⟨9463803562762927940838833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6309202375175285293892555 9463803562762927940838833)
                  ·
                    refine ⟨7097852672072195955629125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9463803562762927940838833 7097852672072195955629125)
                    ·
                      refine ⟨1330847376013536741680461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7097852672072195955629125 1330847376013536741680461)
                      ·
                        rfl

theorem cell23_2591816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3, 1, 2, 4].length) (baseStart_2591816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2591816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2591816 prefixEnd_2591816 := by exact prefixLift 2591816
  have htrace : WordTrace (prefixWord ++ tailWord_2591816) baseStart_2591816 baseEnd_2591816 := by
    simpa [prefixWord, tailWord_2591816, baseEnd_2591816] using wordTrace_append hprefix tailTrace_2591816
  have hstable : (prefixWord ++ tailWord_2591816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591816).length < 2 ^ (prefixWord ++ tailWord_2591816).sum := by decide
  have hdescent : baseEnd_2591816 < baseStart_2591816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591826 : List Nat := [3, 2, 2, 1, 3, 1, 2, 9]
def baseStart_2591826 : Nat := 118140960795 + 2591826 * 2 ^ 59
def prefixEnd_2591826 : Nat := 4983230072969 + 3 ^ 40 * 2591826 * 2
def baseEnd_2591826 : Nat := 49290833734077100094645

theorem tailTrace_2591826 : CollatzResearch.WordTrace tailWord_2591826 prefixEnd_2591826 49290833734077100094645 := by
  unfold tailWord_2591826
  simp only [CollatzResearch.WordTrace]
  refine ⟨23632915077066131371212833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63021106872176350323234221 23632915077066131371212833)
  ·
    refine ⟨17724686307799598528409625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23632915077066131371212833 17724686307799598528409625)
    ·
      refine ⟨13293514730849698896307219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17724686307799598528409625 13293514730849698896307219)
      ·
        refine ⟨19940272096274548344460829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13293514730849698896307219 19940272096274548344460829)
        ·
          refine ⟨7477602036102955629172811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19940272096274548344460829 7477602036102955629172811)
          ·
            refine ⟨11216403054154433443759217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7477602036102955629172811 11216403054154433443759217)
            ·
              refine ⟨8412302290615825082819413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11216403054154433443759217 8412302290615825082819413)
              ·
                refine ⟨49290833734077100094645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8412302290615825082819413 49290833734077100094645)
                ·
                  rfl

theorem cell23_2591826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 9].length) (baseStart_2591826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2591826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2591826 prefixEnd_2591826 := by exact prefixLift 2591826
  have htrace : WordTrace (prefixWord ++ tailWord_2591826) baseStart_2591826 baseEnd_2591826 := by
    simpa [prefixWord, tailWord_2591826, baseEnd_2591826] using wordTrace_append hprefix tailTrace_2591826
  have hstable : (prefixWord ++ tailWord_2591826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591826).length < 2 ^ (prefixWord ++ tailWord_2591826).sum := by decide
  have hdescent : baseEnd_2591826 < baseStart_2591826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591840 : List Nat := [2, 1, 1, 3, 2, 2, 5, 1, 1, 2, 3]
def baseStart_2591840 : Nat := 118140960795 + 2591840 * 2 ^ 59
def prefixEnd_2591840 : Nat := 4983230072969 + 3 ^ 40 * 2591840 * 2
def baseEnd_2591840 : Nat := 1330859699549244647780351

theorem tailTrace_2591840 : CollatzResearch.WordTrace tailWord_2591840 prefixEnd_2591840 1330859699549244647780351 := by
  unfold tailWord_2591840
  simp only [CollatzResearch.WordTrace]
  refine ⟨47266085465106902937930487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63021447286809203917240649 47266085465106902937930487)
  ·
    refine ⟨70899128197660354406895731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47266085465106902937930487 70899128197660354406895731)
    ·
      refine ⟨106348692296490531610343597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70899128197660354406895731 106348692296490531610343597)
      ·
        refine ⟨39880759611183949353878849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106348692296490531610343597 39880759611183949353878849)
        ·
          refine ⟨29910569708387962015409137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39880759611183949353878849 29910569708387962015409137)
          ·
            refine ⟨22432927281290971511556853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29910569708387962015409137 22432927281290971511556853)
            ·
              refine ⟨2103086932621028579208455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22432927281290971511556853 2103086932621028579208455)
              ·
                refine ⟨3154630398931542868812683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2103086932621028579208455 3154630398931542868812683)
                ·
                  refine ⟨4731945598397314303219025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3154630398931542868812683 4731945598397314303219025)
                  ·
                    refine ⟨3548959198797985727414269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4731945598397314303219025 3548959198797985727414269)
                    ·
                      refine ⟨1330859699549244647780351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3548959198797985727414269 1330859699549244647780351)
                      ·
                        rfl

theorem cell23_2591840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 1, 1, 2, 3].length) (baseStart_2591840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2591840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2591840 prefixEnd_2591840 := by exact prefixLift 2591840
  have htrace : WordTrace (prefixWord ++ tailWord_2591840) baseStart_2591840 baseEnd_2591840 := by
    simpa [prefixWord, tailWord_2591840, baseEnd_2591840] using wordTrace_append hprefix tailTrace_2591840
  have hstable : (prefixWord ++ tailWord_2591840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591840).length < 2 ^ (prefixWord ++ tailWord_2591840).sum := by decide
  have hdescent : baseEnd_2591840 < baseStart_2591840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591848 : List Nat := [2, 1, 4, 4, 2, 1, 2, 2, 1, 1, 3]
def baseStart_2591848 : Nat := 118140960795 + 2591848 * 2 ^ 59
def prefixEnd_2591848 : Nat := 4983230072969 + 3 ^ 40 * 2591848 * 2
def baseEnd_2591848 : Nat := 1330863807394480616480315

theorem tailTrace_2591848 : CollatzResearch.WordTrace tailWord_2591848 prefixEnd_2591848 1330863807394480616480315 := by
  unfold tailWord_2591848
  simp only [CollatzResearch.WordTrace]
  refine ⟨47266231357092411621076099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63021641809456548828101465 47266231357092411621076099)
  ·
    refine ⟨70899347035638617431614149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47266231357092411621076099 70899347035638617431614149)
    ·
      refine ⟨13293627569182240768427653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70899347035638617431614149 13293627569182240768427653)
      ·
        refine ⟨2492555169221670144080185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13293627569182240768427653 2492555169221670144080185)
        ·
          refine ⟨1869416376916252608060139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2492555169221670144080185 1869416376916252608060139)
          ·
            refine ⟨2804124565374378912090209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1869416376916252608060139 2804124565374378912090209)
            ·
              refine ⟨2103093424030784184067657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2804124565374378912090209 2103093424030784184067657)
              ·
                refine ⟨1577320068023088138050743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2103093424030784184067657 1577320068023088138050743)
                ·
                  refine ⟨2365980102034632207076115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1577320068023088138050743 2365980102034632207076115)
                  ·
                    refine ⟨3548970153051948310614173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2365980102034632207076115 3548970153051948310614173)
                    ·
                      refine ⟨1330863807394480616480315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3548970153051948310614173 1330863807394480616480315)
                      ·
                        rfl

theorem cell23_2591848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_2591848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2591848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2591848 prefixEnd_2591848 := by exact prefixLift 2591848
  have htrace : WordTrace (prefixWord ++ tailWord_2591848) baseStart_2591848 baseEnd_2591848 := by
    simpa [prefixWord, tailWord_2591848, baseEnd_2591848] using wordTrace_append hprefix tailTrace_2591848
  have hstable : (prefixWord ++ tailWord_2591848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591848).length < 2 ^ (prefixWord ++ tailWord_2591848).sum := by decide
  have hdescent : baseEnd_2591848 < baseStart_2591848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591854 : List Nat := [4, 1, 2, 2, 1, 3, 1, 4, 1, 2, 2]
def baseStart_2591854 : Nat := 118140960795 + 2591854 * 2 ^ 59
def prefixEnd_2591854 : Nat := 4983230072969 + 3 ^ 40 * 2591854 * 2
def baseEnd_2591854 : Nat := 1330866888278407593005287

theorem tailTrace_2591854 : CollatzResearch.WordTrace tailWord_2591854 prefixEnd_2591854 1330866888278407593005287 := by
  unfold tailWord_2591854
  simp only [CollatzResearch.WordTrace]
  refine ⟨11816585194020385783358827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63021787701442057511247077 11816585194020385783358827)
  ·
    refine ⟨17724877791030578675038241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11816585194020385783358827 17724877791030578675038241)
    ·
      refine ⟨13293658343272934006278681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17724877791030578675038241 13293658343272934006278681)
      ·
        refine ⟨9970243757454700504709011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13293658343272934006278681 9970243757454700504709011)
        ·
          refine ⟨14955365636182050757063517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9970243757454700504709011 14955365636182050757063517)
          ·
            refine ⟨5608262113568269033898819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14955365636182050757063517 5608262113568269033898819)
            ·
              refine ⟨8412393170352403550848229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5608262113568269033898819 8412393170352403550848229)
              ·
                refine ⟨1577323719441075665784043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8412393170352403550848229 1577323719441075665784043)
                ·
                  refine ⟨2365985579161613498676065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1577323719441075665784043 2365985579161613498676065)
                  ·
                    refine ⟨1774489184371210124007049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2365985579161613498676065 1774489184371210124007049)
                    ·
                      refine ⟨1330866888278407593005287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1774489184371210124007049 1330866888278407593005287)
                      ·
                        rfl

theorem cell23_2591854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_2591854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2591854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2591854 prefixEnd_2591854 := by exact prefixLift 2591854
  have htrace : WordTrace (prefixWord ++ tailWord_2591854) baseStart_2591854 baseEnd_2591854 := by
    simpa [prefixWord, tailWord_2591854, baseEnd_2591854] using wordTrace_append hprefix tailTrace_2591854
  have hstable : (prefixWord ++ tailWord_2591854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591854).length < 2 ^ (prefixWord ++ tailWord_2591854).sum := by decide
  have hdescent : baseEnd_2591854 < baseStart_2591854 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591863 : List Nat := [1, 1, 3, 1, 1, 4, 1, 1, 5, 3, 2]
def baseStart_2591863 : Nat := 118140960795 + 2591863 * 2 ^ 59
def prefixEnd_2591863 : Nat := 4983230072969 + 3 ^ 40 * 2591863 * 2
def baseEnd_2591863 : Nat := 1330871509604298057792745

theorem tailTrace_2591863 : CollatzResearch.WordTrace tailWord_2591863 prefixEnd_2591863 1330871509604298057792745 := by
  unfold tailWord_2591863
  simp only [CollatzResearch.WordTrace]
  refine ⟨94533009809130480803948243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63022006539420320535965495 94533009809130480803948243)
  ·
    refine ⟨141799514713695721205922365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94533009809130480803948243 141799514713695721205922365)
    ·
      refine ⟨53174818017635895452220887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141799514713695721205922365 53174818017635895452220887)
      ·
        refine ⟨79762227026453843178331331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53174818017635895452220887 79762227026453843178331331)
        ·
          refine ⟨119643340539680764767496997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79762227026453843178331331 119643340539680764767496997)
          ·
            refine ⟨22433126351190143393905687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 119643340539680764767496997 22433126351190143393905687)
            ·
              refine ⟨33649689526785215090858531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22433126351190143393905687 33649689526785215090858531)
              ·
                refine ⟨50474534290177822636287797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33649689526785215090858531 50474534290177822636287797)
                ·
                  refine ⟨4731987589704170872151981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50474534290177822636287797 4731987589704170872151981)
                  ·
                    refine ⟨1774495346139064077056993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4731987589704170872151981 1774495346139064077056993)
                    ·
                      refine ⟨1330871509604298057792745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1774495346139064077056993 1330871509604298057792745)
                      ·
                        rfl

theorem cell23_2591863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 5, 3, 2].length) (baseStart_2591863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2591863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2591863 prefixEnd_2591863 := by exact prefixLift 2591863
  have htrace : WordTrace (prefixWord ++ tailWord_2591863) baseStart_2591863 baseEnd_2591863 := by
    simpa [prefixWord, tailWord_2591863, baseEnd_2591863] using wordTrace_append hprefix tailTrace_2591863
  have hstable : (prefixWord ++ tailWord_2591863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591863).length < 2 ^ (prefixWord ++ tailWord_2591863).sum := by decide
  have hdescent : baseEnd_2591863 < baseStart_2591863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591893 : List Nat := [1, 3, 2, 1, 1, 1, 2, 3, 3, 4, 2]
def baseStart_2591893 : Nat := 118140960795 + 2591893 * 2 ^ 59
def prefixEnd_2591893 : Nat := 4983230072969 + 3 ^ 40 * 2591893 * 2
def baseEnd_2591893 : Nat := 1330886914023932940417607

theorem tailTrace_2591893 : CollatzResearch.WordTrace tailWord_2591893 prefixEnd_2591893 1330886914023932940417607 := by
  unfold tailWord_2591893
  simp only [CollatzResearch.WordTrace]
  refine ⟨94534103999021795927540333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63022735999347863951693555 94534103999021795927540333)
  ·
    refine ⟨35450288999633173472827625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94534103999021795927540333 35450288999633173472827625)
    ·
      refine ⟨26587716749724880104620719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35450288999633173472827625 26587716749724880104620719)
      ·
        refine ⟨39881575124587320156931079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26587716749724880104620719 39881575124587320156931079)
        ·
          refine ⟨59822362686880980235396619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39881575124587320156931079 59822362686880980235396619)
          ·
            refine ⟨89733544030321470353094929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59822362686880980235396619 89733544030321470353094929)
            ·
              refine ⟨67300158022741102764821197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89733544030321470353094929 67300158022741102764821197)
              ·
                refine ⟨25237559258527913536807949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67300158022741102764821197 25237559258527913536807949)
                ·
                  refine ⟨9464084721947967576302981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25237559258527913536807949 9464084721947967576302981)
                  ·
                    refine ⟨1774515885365243920556809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9464084721947967576302981 1774515885365243920556809)
                    ·
                      refine ⟨1330886914023932940417607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1774515885365243920556809 1330886914023932940417607)
                      ·
                        rfl

theorem cell23_2591893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3, 4, 2].length) (baseStart_2591893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2591893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2591893 prefixEnd_2591893 := by exact prefixLift 2591893
  have htrace : WordTrace (prefixWord ++ tailWord_2591893) baseStart_2591893 baseEnd_2591893 := by
    simpa [prefixWord, tailWord_2591893, baseEnd_2591893] using wordTrace_append hprefix tailTrace_2591893
  have hstable : (prefixWord ++ tailWord_2591893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591893).length < 2 ^ (prefixWord ++ tailWord_2591893).sum := by decide
  have hdescent : baseEnd_2591893 < baseStart_2591893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591953 : List Nat := [1, 2, 2, 1, 2, 2, 1, 2, 1, 7, 2]
def baseStart_2591953 : Nat := 118140960795 + 2591953 * 2 ^ 59
def prefixEnd_2591953 : Nat := 4983230072969 + 3 ^ 40 * 2591953 * 2
def baseEnd_2591953 : Nat := 1330917722863202705667331

theorem tailTrace_2591953 : CollatzResearch.WordTrace tailWord_2591953 prefixEnd_2591953 1330917722863202705667331 := by
  unfold tailWord_2591953
  simp only [CollatzResearch.WordTrace]
  refine ⟨94536292378804426174724513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63024194919202950783149675 94536292378804426174724513)
  ·
    refine ⟨70902219284103319631043385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94536292378804426174724513 70902219284103319631043385)
    ·
      refine ⟨53176664463077489723282539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70902219284103319631043385 53176664463077489723282539)
      ·
        refine ⟨79764996694616234584923809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53176664463077489723282539 79764996694616234584923809)
        ·
          refine ⟨59823747520962175938692857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79764996694616234584923809 59823747520962175938692857)
          ·
            refine ⟨44867810640721631954019643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59823747520962175938692857 44867810640721631954019643)
            ·
              refine ⟨67301715961082447931029465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44867810640721631954019643 67301715961082447931029465)
              ·
                refine ⟨50476286970811835948272099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67301715961082447931029465 50476286970811835948272099)
                ·
                  refine ⟨75714430456217753922408149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50476286970811835948272099 75714430456217753922408149)
                  ·
                    refine ⟨1774556963817603607556441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 75714430456217753922408149 1774556963817603607556441)
                    ·
                      refine ⟨1330917722863202705667331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1774556963817603607556441 1330917722863202705667331)
                      ·
                        rfl

theorem cell23_2591953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 7, 2].length) (baseStart_2591953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2591953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2591953 prefixEnd_2591953 := by exact prefixLift 2591953
  have htrace : WordTrace (prefixWord ++ tailWord_2591953) baseStart_2591953 baseEnd_2591953 := by
    simpa [prefixWord, tailWord_2591953, baseEnd_2591953] using wordTrace_append hprefix tailTrace_2591953
  have hstable : (prefixWord ++ tailWord_2591953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591953).length < 2 ^ (prefixWord ++ tailWord_2591953).sum := by decide
  have hdescent : baseEnd_2591953 < baseStart_2591953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2591993 : List Nat := [1, 2, 1, 3, 1, 1, 4, 1, 5, 4]
def baseStart_2591993 : Nat := 118140960795 + 2591993 * 2 ^ 59
def prefixEnd_2591993 : Nat := 4983230072969 + 3 ^ 40 * 2591993 * 2
def baseEnd_2591993 : Nat := 443646087363127516389049

theorem tailTrace_2591993 : CollatzResearch.WordTrace tailWord_2591993 prefixEnd_2591993 443646087363127516389049 := by
  unfold tailWord_2591993
  simp only [CollatzResearch.WordTrace]
  refine ⟨94537751298659513006180633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63025167532439675337453755 94537751298659513006180633)
  ·
    refine ⟨70903313473994634754635475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94537751298659513006180633 70903313473994634754635475)
    ·
      refine ⟨106354970210991952131953213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70903313473994634754635475 106354970210991952131953213)
      ·
        refine ⟨39883113829121982049482455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106354970210991952131953213 39883113829121982049482455)
        ·
          refine ⟨59824670743682973074223683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39883113829121982049482455 59824670743682973074223683)
          ·
            refine ⟨89737006115524459611335525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59824670743682973074223683 89737006115524459611335525)
            ·
              refine ⟨16825688646660836177125411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89737006115524459611335525 16825688646660836177125411)
              ·
                refine ⟨25238532969991254265688117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16825688646660836177125411 25238532969991254265688117)
                ·
                  refine ⟨2366112465936680087408261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25238532969991254265688117 2366112465936680087408261)
                  ·
                    refine ⟨443646087363127516389049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2366112465936680087408261 443646087363127516389049)
                    ·
                      rfl

theorem cell23_2591993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 5, 4].length) (baseStart_2591993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2591993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2591993 prefixEnd_2591993 := by exact prefixLift 2591993
  have htrace : WordTrace (prefixWord ++ tailWord_2591993) baseStart_2591993 baseEnd_2591993 := by
    simpa [prefixWord, tailWord_2591993, baseEnd_2591993] using wordTrace_append hprefix tailTrace_2591993
  have hstable : (prefixWord ++ tailWord_2591993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2591993).length < 2 ^ (prefixWord ++ tailWord_2591993).sum := by decide
  have hdescent : baseEnd_2591993 < baseStart_2591993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2591993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592018 : List Nat := [3, 2, 4, 2, 2, 1, 2, 2, 5]
def baseStart_2592018 : Nat := 118140960795 + 2592018 * 2 ^ 59
def prefixEnd_2592018 : Nat := 4983230072969 + 3 ^ 40 * 2592018 * 2
def baseEnd_2592018 : Nat := 147883455456193883483837

theorem tailTrace_2592018 : CollatzResearch.WordTrace tailWord_2592018 prefixEnd_2592018 147883455456193883483837 := by
  unfold tailWord_2592018
  simp only [CollatzResearch.WordTrace]
  refine ⟨23634665780892235568960177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63025775415712628183893805 23634665780892235568960177)
  ·
    refine ⟨17725999335669176676720133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23634665780892235568960177 17725999335669176676720133)
    ·
      refine ⟨3323624875437970626885025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17725999335669176676720133 3323624875437970626885025)
      ·
        refine ⟨2492718656578477970163769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3323624875437970626885025 2492718656578477970163769)
        ·
          refine ⟨1869538992433858477622827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2492718656578477970163769 1869538992433858477622827)
          ·
            refine ⟨2804308488650787716434241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1869538992433858477622827 2804308488650787716434241)
            ·
              refine ⟨2103231366488090787325681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2804308488650787716434241 2103231366488090787325681)
              ·
                refine ⟨1577423524866068090494261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2103231366488090787325681 1577423524866068090494261)
                ·
                  refine ⟨147883455456193883483837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1577423524866068090494261 147883455456193883483837)
                  ·
                    rfl

theorem cell23_2592018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 2, 5].length) (baseStart_2592018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2592018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2592018 prefixEnd_2592018 := by exact prefixLift 2592018
  have htrace : WordTrace (prefixWord ++ tailWord_2592018) baseStart_2592018 baseEnd_2592018 := by
    simpa [prefixWord, tailWord_2592018, baseEnd_2592018] using wordTrace_append hprefix tailTrace_2592018
  have hstable : (prefixWord ++ tailWord_2592018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592018).length < 2 ^ (prefixWord ++ tailWord_2592018).sum := by decide
  have hdescent : baseEnd_2592018 < baseStart_2592018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592033 : List Nat := [1, 2, 3, 2, 1, 1, 1, 2, 2, 5, 3]
def baseStart_2592033 : Nat := 118140960795 + 2592033 * 2 ^ 59
def prefixEnd_2592033 : Nat := 4983230072969 + 3 ^ 40 * 2592033 * 2
def baseEnd_2592033 : Nat := 1330958801315562392666963

theorem tailTrace_2592033 : CollatzResearch.WordTrace tailWord_2592033 prefixEnd_2592033 1330958801315562392666963 := by
  unfold tailWord_2592033
  simp only [CollatzResearch.WordTrace]
  refine ⟨94539210218514599837636753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63026140145676399891757835 94539210218514599837636753)
  ·
    refine ⟨70904407663885949878227565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94539210218514599837636753 70904407663885949878227565)
    ·
      refine ⟨26589152873957231204335337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70904407663885949878227565 26589152873957231204335337)
      ·
        refine ⟨19941864655467923403251503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26589152873957231204335337 19941864655467923403251503)
        ·
          refine ⟨29912796983201885104877255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19941864655467923403251503 29912796983201885104877255)
          ·
            refine ⟨44869195474802827657315883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29912796983201885104877255 44869195474802827657315883)
            ·
              refine ⟨67303793212204241485973825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44869195474802827657315883 67303793212204241485973825)
              ·
                refine ⟨50477844909153181114480369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67303793212204241485973825 50477844909153181114480369)
                ·
                  refine ⟨37858383681864885835860277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50477844909153181114480369 37858383681864885835860277)
                  ·
                    refine ⟨3549223470174833047111901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37858383681864885835860277 3549223470174833047111901)
                    ·
                      refine ⟨1330958801315562392666963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3549223470174833047111901 1330958801315562392666963)
                      ·
                        rfl

theorem cell23_2592033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_2592033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2592033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2592033 prefixEnd_2592033 := by exact prefixLift 2592033
  have htrace : WordTrace (prefixWord ++ tailWord_2592033) baseStart_2592033 baseEnd_2592033 := by
    simpa [prefixWord, tailWord_2592033, baseEnd_2592033] using wordTrace_append hprefix tailTrace_2592033
  have hstable : (prefixWord ++ tailWord_2592033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592033).length < 2 ^ (prefixWord ++ tailWord_2592033).sum := by decide
  have hdescent : baseEnd_2592033 < baseStart_2592033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592040 : List Nat := [2, 1, 5, 1, 2, 1, 2, 3, 6]
def baseStart_2592040 : Nat := 118140960795 + 2592040 * 2 ^ 59
def prefixEnd_2592040 : Nat := 4983230072969 + 3 ^ 40 * 2592040 * 2
def baseEnd_2592040 : Nat := 147884710631127096142159

theorem tailTrace_2592040 : CollatzResearch.WordTrace tailWord_2592040 prefixEnd_2592040 147884710631127096142159 := by
  unfold tailWord_2592040
  simp only [CollatzResearch.WordTrace]
  refine ⟨47269732764744620016570787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63026310352992826688761049 47269732764744620016570787)
  ·
    refine ⟨70904599147116930024856181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47269732764744620016570787 70904599147116930024856181)
    ·
      refine ⟨6647306170042212189830267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70904599147116930024856181 6647306170042212189830267)
      ·
        refine ⟨9970959255063318284745401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6647306170042212189830267 9970959255063318284745401)
        ·
          refine ⟨7478219441297488713559051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9970959255063318284745401 7478219441297488713559051)
          ·
            refine ⟨11217329161946233070338577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7478219441297488713559051 11217329161946233070338577)
            ·
              refine ⟨8412996871459674802753933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11217329161946233070338577 8412996871459674802753933)
              ·
                refine ⟨3154873826797378051032725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8412996871459674802753933 3154873826797378051032725)
                ·
                  refine ⟨147884710631127096142159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3154873826797378051032725 147884710631127096142159)
                  ·
                    rfl

theorem cell23_2592040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 3, 6].length) (baseStart_2592040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2592040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2592040 prefixEnd_2592040 := by exact prefixLift 2592040
  have htrace : WordTrace (prefixWord ++ tailWord_2592040) baseStart_2592040 baseEnd_2592040 := by
    simpa [prefixWord, tailWord_2592040, baseEnd_2592040] using wordTrace_append hprefix tailTrace_2592040
  have hstable : (prefixWord ++ tailWord_2592040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592040).length < 2 ^ (prefixWord ++ tailWord_2592040).sum := by decide
  have hdescent : baseEnd_2592040 < baseStart_2592040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592054 : List Nat := [5, 1, 2, 3, 1, 1, 1, 1, 1, 4, 3]
def baseStart_2592054 : Nat := 118140960795 + 2592054 * 2 ^ 59
def prefixEnd_2592054 : Nat := 4983230072969 + 3 ^ 40 * 2592054 * 2
def baseEnd_2592054 : Nat := 1330969584409306810504367

theorem tailTrace_2592054 : CollatzResearch.WordTrace tailWord_2592054 prefixEnd_2592054 1330969584409306810504367 := by
  unfold tailWord_2592054
  simp only [CollatzResearch.WordTrace]
  refine ⟨5908748509464907526509451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63026650767625680282767477 5908748509464907526509451)
  ·
    refine ⟨8863122764197361289764177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5908748509464907526509451 8863122764197361289764177)
    ·
      refine ⟨6647342073148020967323133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8863122764197361289764177 6647342073148020967323133)
      ·
        refine ⟨2492753277430507862746175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6647342073148020967323133 2492753277430507862746175)
        ·
          refine ⟨3739129916145761794119263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2492753277430507862746175 3739129916145761794119263)
          ·
            refine ⟨5608694874218642691178895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3739129916145761794119263 5608694874218642691178895)
            ·
              refine ⟨8413042311327964036768343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5608694874218642691178895 8413042311327964036768343)
              ·
                refine ⟨12619563466991946055152515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8413042311327964036768343 12619563466991946055152515)
                ·
                  refine ⟨18929345200487919082728773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12619563466991946055152515 18929345200487919082728773)
                  ·
                    refine ⟨3549252225091484828011645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18929345200487919082728773 3549252225091484828011645)
                    ·
                      refine ⟨1330969584409306810504367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3549252225091484828011645 1330969584409306810504367)
                      ·
                        rfl

theorem cell23_2592054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_2592054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2592054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2592054 prefixEnd_2592054 := by exact prefixLift 2592054
  have htrace : WordTrace (prefixWord ++ tailWord_2592054) baseStart_2592054 baseEnd_2592054 := by
    simpa [prefixWord, tailWord_2592054, baseEnd_2592054] using wordTrace_append hprefix tailTrace_2592054
  have hstable : (prefixWord ++ tailWord_2592054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592054).length < 2 ^ (prefixWord ++ tailWord_2592054).sum := by decide
  have hdescent : baseEnd_2592054 < baseStart_2592054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592061 : List Nat := [1, 4, 1, 5, 1, 1, 2, 3, 1, 4]
def baseStart_2592061 : Nat := 118140960795 + 2592061 * 2 ^ 59
def prefixEnd_2592061 : Nat := 4983230072969 + 3 ^ 40 * 2592061 * 2
def baseEnd_2592061 : Nat := 443657726257962761038945

theorem tailTrace_2592061 : CollatzResearch.WordTrace tailWord_2592061 prefixEnd_2592061 443657726257962761038945 := by
  unfold tailWord_2592061
  simp only [CollatzResearch.WordTrace]
  refine ⟨94540231462413160619656037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63026820974942107079770691 94540231462413160619656037)
  ·
    refine ⟨17726293399202467616185507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94540231462413160619656037 17726293399202467616185507)
    ·
      refine ⟨26589440098803701424278261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17726293399202467616185507 26589440098803701424278261)
      ·
        refine ⟨2492760009262847008526087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26589440098803701424278261 2492760009262847008526087)
        ·
          refine ⟨3739140013894270512789131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2492760009262847008526087 3739140013894270512789131)
          ·
            refine ⟨5608710020841405769183697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3739140013894270512789131 5608710020841405769183697)
            ·
              refine ⟨4206532515631054326887773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5608710020841405769183697 4206532515631054326887773)
              ·
                refine ⟨1577449693361645372582915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4206532515631054326887773 1577449693361645372582915)
                ·
                  refine ⟨2366174540042468058874373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1577449693361645372582915 2366174540042468058874373)
                  ·
                    refine ⟨443657726257962761038945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2366174540042468058874373 443657726257962761038945)
                    ·
                      rfl

theorem cell23_2592061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 3, 1, 4].length) (baseStart_2592061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2592061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2592061 prefixEnd_2592061 := by exact prefixLift 2592061
  have htrace : WordTrace (prefixWord ++ tailWord_2592061) baseStart_2592061 baseEnd_2592061 := by
    simpa [prefixWord, tailWord_2592061, baseEnd_2592061] using wordTrace_append hprefix tailTrace_2592061
  have hstable : (prefixWord ++ tailWord_2592061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592061).length < 2 ^ (prefixWord ++ tailWord_2592061).sum := by decide
  have hdescent : baseEnd_2592061 < baseStart_2592061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592084 : List Nat := [2, 4, 1, 1, 2, 1, 1, 6, 1, 1, 3]
def baseStart_2592084 : Nat := 118140960795 + 2592084 * 2 ^ 59
def prefixEnd_2592084 : Nat := 4983230072969 + 3 ^ 40 * 2592084 * 2
def baseEnd_2592084 : Nat := 1330984988828941693129229

theorem tailTrace_2592084 : CollatzResearch.WordTrace tailWord_2592084 prefixEnd_2592084 1330984988828941693129229 := by
  unfold tailWord_2592084
  simp only [CollatzResearch.WordTrace]
  refine ⟨47270535170664917773871653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63027380227553223698495537 47270535170664917773871653)
  ·
    refine ⟨8863225344499672082600935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47270535170664917773871653 8863225344499672082600935)
    ·
      refine ⟨13294838016749508123901403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8863225344499672082600935 13294838016749508123901403)
      ·
        refine ⟨19942257025124262185852105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13294838016749508123901403 19942257025124262185852105)
        ·
          refine ⟨14956692768843196639389079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19942257025124262185852105 14956692768843196639389079)
          ·
            refine ⟨22435039153264794959083619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14956692768843196639389079 22435039153264794959083619)
            ·
              refine ⟨33652558729897192438625429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22435039153264794959083619 33652558729897192438625429)
              ·
                refine ⟨1577463690463930895560567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33652558729897192438625429 1577463690463930895560567)
                ·
                  refine ⟨2366195535695896343340851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1577463690463930895560567 2366195535695896343340851)
                  ·
                    refine ⟨3549293303543844515011277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2366195535695896343340851 3549293303543844515011277)
                    ·
                      refine ⟨1330984988828941693129229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3549293303543844515011277 1330984988828941693129229)
                      ·
                        rfl

theorem cell23_2592084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 6, 1, 1, 3].length) (baseStart_2592084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2592084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2592084 prefixEnd_2592084 := by exact prefixLift 2592084
  have htrace : WordTrace (prefixWord ++ tailWord_2592084) baseStart_2592084 baseEnd_2592084 := by
    simpa [prefixWord, tailWord_2592084, baseEnd_2592084] using wordTrace_append hprefix tailTrace_2592084
  have hstable : (prefixWord ++ tailWord_2592084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592084).length < 2 ^ (prefixWord ++ tailWord_2592084).sum := by decide
  have hdescent : baseEnd_2592084 < baseStart_2592084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592100 : List Nat := [2, 3, 1, 1, 3, 2, 3, 1, 1, 6]
def baseStart_2592100 : Nat := 118140960795 + 2592100 * 2 ^ 59
def prefixEnd_2592100 : Nat := 4983230072969 + 3 ^ 40 * 2592100 * 2
def baseEnd_2592100 : Nat := 443664401506471210176385

theorem tailTrace_2592100 : CollatzResearch.WordTrace tailWord_2592100 prefixEnd_2592100 443664401506471210176385 := by
  unfold tailWord_2592100
  simp only [CollatzResearch.WordTrace]
  refine ⟨47270826954635935140162877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63027769272847913520217169 47270826954635935140162877)
  ·
    refine ⟨17726560107988475677561079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47270826954635935140162877 17726560107988475677561079)
    ·
      refine ⟨26589840161982713516341619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17726560107988475677561079 26589840161982713516341619)
      ·
        refine ⟨39884760242974070274512429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26589840161982713516341619 39884760242974070274512429)
        ·
          refine ⟨14956785091115276352942161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39884760242974070274512429 14956785091115276352942161)
          ·
            refine ⟨11217588818336457264706621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14956785091115276352942161 11217588818336457264706621)
            ·
              refine ⟨4206595806876171474264983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11217588818336457264706621 4206595806876171474264983)
              ·
                refine ⟨6309893710314257211397475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4206595806876171474264983 6309893710314257211397475)
                ·
                  refine ⟨9464840565471385817096213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6309893710314257211397475 9464840565471385817096213)
                  ·
                    refine ⟨443664401506471210176385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9464840565471385817096213 443664401506471210176385)
                    ·
                      rfl

theorem cell23_2592100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 1, 1, 6].length) (baseStart_2592100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2592100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2592100 prefixEnd_2592100 := by exact prefixLift 2592100
  have htrace : WordTrace (prefixWord ++ tailWord_2592100) baseStart_2592100 baseEnd_2592100 := by
    simpa [prefixWord, tailWord_2592100, baseEnd_2592100] using wordTrace_append hprefix tailTrace_2592100
  have hstable : (prefixWord ++ tailWord_2592100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592100).length < 2 ^ (prefixWord ++ tailWord_2592100).sum := by decide
  have hdescent : baseEnd_2592100 < baseStart_2592100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592158 : List Nat := [4, 3, 1, 2, 3, 1, 1, 2, 1, 1, 4]
def baseStart_2592158 : Nat := 118140960795 + 2592158 * 2 ^ 59
def prefixEnd_2592158 : Nat := 4983230072969 + 3 ^ 40 * 2592158 * 2
def baseEnd_2592158 : Nat := 1331022986397374403603889

theorem tailTrace_2592158 : CollatzResearch.WordTrace tailWord_2592158 prefixEnd_2592158 1331022986397374403603889 := by
  unfold tailWord_2592158
  simp only [CollatzResearch.WordTrace]
  refine ⟨11817971167882718273242141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63029179562041164123958085 11817971167882718273242141)
  ·
    refine ⟨4431739187956019352465803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11817971167882718273242141 4431739187956019352465803)
    ·
      refine ⟨6647608781934029028698705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4431739187956019352465803 6647608781934029028698705)
      ·
        refine ⟨4985706586450521771524029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6647608781934029028698705 4985706586450521771524029)
        ·
          refine ⟨1869639969918945664321511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4985706586450521771524029 1869639969918945664321511)
          ·
            refine ⟨2804459954878418496482267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1869639969918945664321511 2804459954878418496482267)
            ·
              refine ⟨4206689932317627744723401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2804459954878418496482267 4206689932317627744723401)
              ·
                refine ⟨3155017449238220808542551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4206689932317627744723401 3155017449238220808542551)
                ·
                  refine ⟨4732526173857331212813827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3155017449238220808542551 4732526173857331212813827)
                  ·
                    refine ⟨7098789260785996819220741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4732526173857331212813827 7098789260785996819220741)
                    ·
                      refine ⟨1331022986397374403603889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7098789260785996819220741 1331022986397374403603889)
                      ·
                        rfl

theorem cell23_2592158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_2592158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2592158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2592158 prefixEnd_2592158 := by exact prefixLift 2592158
  have htrace : WordTrace (prefixWord ++ tailWord_2592158) baseStart_2592158 baseEnd_2592158 := by
    simpa [prefixWord, tailWord_2592158, baseEnd_2592158] using wordTrace_append hprefix tailTrace_2592158
  have hstable : (prefixWord ++ tailWord_2592158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592158).length < 2 ^ (prefixWord ++ tailWord_2592158).sum := by decide
  have hdescent : baseEnd_2592158 < baseStart_2592158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592190 : List Nat := [4, 2, 1, 1, 1, 1, 1, 4, 2, 6]
def baseStart_2592190 : Nat := 118140960795 + 2592190 * 2 ^ 59
def prefixEnd_2592190 : Nat := 4983230072969 + 3 ^ 40 * 2592190 * 2
def baseEnd_2592190 : Nat := 443679805926106092801247

theorem tailTrace_2592190 : CollatzResearch.WordTrace tailWord_2592190 prefixEnd_2592190 443679805926106092801247 := by
  unfold tailWord_2592190
  simp only [CollatzResearch.WordTrace]
  refine ⟨11818117059868226956387753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63029957652630543767401349 11818117059868226956387753)
  ·
    refine ⟨8863587794901170217290815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11818117059868226956387753 8863587794901170217290815)
    ·
      refine ⟨13295381692351755325936223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8863587794901170217290815 13295381692351755325936223)
      ·
        refine ⟨19943072538527632988904335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13295381692351755325936223 19943072538527632988904335)
        ·
          refine ⟨29914608807791449483356503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19943072538527632988904335 29914608807791449483356503)
          ·
            refine ⟨44871913211687174225034755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29914608807791449483356503 44871913211687174225034755)
            ·
              refine ⟨67307869817530761337552133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44871913211687174225034755 67307869817530761337552133)
              ·
                refine ⟨12620225590787017750791025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67307869817530761337552133 12620225590787017750791025)
                ·
                  refine ⟨9465169193090263313093269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12620225590787017750791025 9465169193090263313093269)
                  ·
                    refine ⟨443679805926106092801247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9465169193090263313093269 443679805926106092801247)
                    ·
                      rfl

theorem cell23_2592190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_2592190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2592190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2592190 prefixEnd_2592190 := by exact prefixLift 2592190
  have htrace : WordTrace (prefixWord ++ tailWord_2592190) baseStart_2592190 baseEnd_2592190 := by
    simpa [prefixWord, tailWord_2592190, baseEnd_2592190] using wordTrace_append hprefix tailTrace_2592190
  have hstable : (prefixWord ++ tailWord_2592190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592190).length < 2 ^ (prefixWord ++ tailWord_2592190).sum := by decide
  have hdescent : baseEnd_2592190 < baseStart_2592190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592200 : List Nat := [2, 1, 3, 1, 3, 1, 1, 1, 1, 6, 3]
def baseStart_2592200 : Nat := 118140960795 + 2592200 * 2 ^ 59
def prefixEnd_2592200 : Nat := 4983230072969 + 3 ^ 40 * 2592200 * 2
def baseEnd_2592200 : Nat := 1331044552584863239278695

theorem tailTrace_2592200 : CollatzResearch.WordTrace tailWord_2592200 prefixEnd_2592200 1331044552584863239278695 := by
  unfold tailWord_2592200
  simp only [CollatzResearch.WordTrace]
  refine ⟨47272650604454793679483027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63030200805939724905977369 47272650604454793679483027)
  ·
    refine ⟨70908975906682190519224541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47272650604454793679483027 70908975906682190519224541)
    ·
      refine ⟨26590865965005821444709203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70908975906682190519224541 26590865965005821444709203)
      ·
        refine ⟨39886298947508732167063805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26590865965005821444709203 39886298947508732167063805)
        ·
          refine ⟨14957362105315774562648927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39886298947508732167063805 14957362105315774562648927)
          ·
            refine ⟨22436043157973661843973391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14957362105315774562648927 22436043157973661843973391)
            ·
              refine ⟨33654064736960492765960087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22436043157973661843973391 33654064736960492765960087)
              ·
                refine ⟨50481097105440739148940131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33654064736960492765960087 50481097105440739148940131)
                ·
                  refine ⟨75721645658161108723410197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50481097105440739148940131 75721645658161108723410197)
                  ·
                    refine ⟨3549452140226301971409853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 75721645658161108723410197 3549452140226301971409853)
                    ·
                      refine ⟨1331044552584863239278695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3549452140226301971409853 1331044552584863239278695)
                      ·
                        rfl

theorem cell23_2592200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 1, 6, 3].length) (baseStart_2592200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2592200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2592200 prefixEnd_2592200 := by exact prefixLift 2592200
  have htrace : WordTrace (prefixWord ++ tailWord_2592200) baseStart_2592200 baseEnd_2592200 := by
    simpa [prefixWord, tailWord_2592200, baseEnd_2592200] using wordTrace_append hprefix tailTrace_2592200
  have hstable : (prefixWord ++ tailWord_2592200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592200).length < 2 ^ (prefixWord ++ tailWord_2592200).sum := by decide
  have hdescent : baseEnd_2592200 < baseStart_2592200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592250 : List Nat := [3, 1, 1, 1, 1, 2, 4, 1, 4, 5]
def baseStart_2592250 : Nat := 118140960795 + 2592250 * 2 ^ 59
def prefixEnd_2592250 : Nat := 4983230072969 + 3 ^ 40 * 2592250 * 2
def baseEnd_2592250 : Nat := 443690075539196014551155

theorem tailTrace_2592250 : CollatzResearch.WordTrace tailWord_2592250 prefixEnd_2592250 443690075539196014551155 := by
  unfold tailWord_2592250
  simp only [CollatzResearch.WordTrace]
  refine ⟨23636781214682111474571551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63031416572485630598857469 23636781214682111474571551)
  ·
    refine ⟨35455171822023167211857327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23636781214682111474571551 35455171822023167211857327)
    ·
      refine ⟨53182757733034750817785991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35455171822023167211857327 53182757733034750817785991)
      ·
        refine ⟨79774136599552126226678987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53182757733034750817785991 79774136599552126226678987)
        ·
          refine ⟨119661204899328189340018481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79774136599552126226678987 119661204899328189340018481)
          ·
            refine ⟨89745903674496142005013861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119661204899328189340018481 89745903674496142005013861)
            ·
              refine ⟨16827356938968026625940099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89745903674496142005013861 16827356938968026625940099)
              ·
                refine ⟨25241035408452039938910149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16827356938968026625940099 25241035408452039938910149)
                ·
                  refine ⟨4732694139084757488545653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25241035408452039938910149 4732694139084757488545653)
                  ·
                    refine ⟨443690075539196014551155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4732694139084757488545653 443690075539196014551155)
                    ·
                      rfl

theorem cell23_2592250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 4, 5].length) (baseStart_2592250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2592250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2592250 prefixEnd_2592250 := by exact prefixLift 2592250
  have htrace : WordTrace (prefixWord ++ tailWord_2592250) baseStart_2592250 baseEnd_2592250 := by
    simpa [prefixWord, tailWord_2592250, baseEnd_2592250] using wordTrace_append hprefix tailTrace_2592250
  have hstable : (prefixWord ++ tailWord_2592250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592250).length < 2 ^ (prefixWord ++ tailWord_2592250).sum := by decide
  have hdescent : baseEnd_2592250 < baseStart_2592250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592287 : List Nat := [1, 1, 2, 4, 1, 1, 2, 2, 1, 6, 2]
def baseStart_2592287 : Nat := 118140960795 + 2592287 * 2 ^ 59
def prefixEnd_2592287 : Nat := 4983230072969 + 3 ^ 40 * 2592287 * 2
def baseEnd_2592287 : Nat := 1331089225401804398890795

theorem tailTrace_2592287 : CollatzResearch.WordTrace tailWord_2592287 prefixEnd_2592287 1331089225401804398890795 := by
  unfold tailWord_2592287
  simp only [CollatzResearch.WordTrace]
  refine ⟨94548474359594401217383115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63032316239729600811588743 94548474359594401217383115)
  ·
    refine ⟨141822711539391601826074673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94548474359594401217383115 141822711539391601826074673)
    ·
      refine ⟨106367033654543701369556005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141822711539391601826074673 106367033654543701369556005)
      ·
        refine ⟨19943818810226944006791751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106367033654543701369556005 19943818810226944006791751)
        ·
          refine ⟨29915728215340416010187627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19943818810226944006791751 29915728215340416010187627)
          ·
            refine ⟨44873592323010624015281441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29915728215340416010187627 44873592323010624015281441)
            ·
              refine ⟨33655194242257968011461081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44873592323010624015281441 33655194242257968011461081)
              ·
                refine ⟨25241395681693476008595811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33655194242257968011461081 25241395681693476008595811)
                ·
                  refine ⟨37862093522540214012893717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25241395681693476008595811 37862093522540214012893717)
                  ·
                    refine ⟨1774785633869072531854393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 37862093522540214012893717 1774785633869072531854393)
                    ·
                      refine ⟨1331089225401804398890795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1774785633869072531854393 1331089225401804398890795)
                      ·
                        rfl

theorem cell23_2592287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 6, 2].length) (baseStart_2592287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2592287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2592287 prefixEnd_2592287 := by exact prefixLift 2592287
  have htrace : WordTrace (prefixWord ++ tailWord_2592287) baseStart_2592287 baseEnd_2592287 := by
    simpa [prefixWord, tailWord_2592287, baseEnd_2592287] using wordTrace_append hprefix tailTrace_2592287
  have hstable : (prefixWord ++ tailWord_2592287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592287).length < 2 ^ (prefixWord ++ tailWord_2592287).sum := by decide
  have hdescent : baseEnd_2592287 < baseStart_2592287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592307 : List Nat := [1, 1, 1, 2, 4, 3, 1, 1, 4, 2, 3]
def baseStart_2592307 : Nat := 118140960795 + 2592307 * 2 ^ 59
def prefixEnd_2592307 : Nat := 4983230072969 + 3 ^ 40 * 2592307 * 2
def baseEnd_2592307 : Nat := 1331099495014894320640703

theorem tailTrace_2592307 : CollatzResearch.WordTrace tailWord_2592307 prefixEnd_2592307 1331099495014894320640703 := by
  unfold tailWord_2592307
  simp only [CollatzResearch.WordTrace]
  refine ⟨94549203819521944633111175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63032802546347963088740783 94549203819521944633111175)
  ·
    refine ⟨141823805729282916949666763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94549203819521944633111175 141823805729282916949666763)
    ·
      refine ⟨212735708593924375424500145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141823805729282916949666763 212735708593924375424500145)
      ·
        refine ⟨159551781445443281568375109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212735708593924375424500145 159551781445443281568375109)
        ·
          refine ⟨29915959021020615294070333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 159551781445443281568375109 29915959021020615294070333)
          ·
            refine ⟨11218484632882730735276375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29915959021020615294070333 11218484632882730735276375)
            ·
              refine ⟨16827726949324096102914563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11218484632882730735276375 16827726949324096102914563)
              ·
                refine ⟨25241590423986144154371845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16827726949324096102914563 25241590423986144154371845)
                ·
                  refine ⟨4732798204497402028944721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25241590423986144154371845 4732798204497402028944721)
                  ·
                    refine ⟨3549598653373051521708541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4732798204497402028944721 3549598653373051521708541)
                    ·
                      refine ⟨1331099495014894320640703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3549598653373051521708541 1331099495014894320640703)
                      ·
                        rfl

theorem cell23_2592307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 4, 2, 3].length) (baseStart_2592307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2592307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2592307 prefixEnd_2592307 := by exact prefixLift 2592307
  have htrace : WordTrace (prefixWord ++ tailWord_2592307) baseStart_2592307 baseEnd_2592307 := by
    simpa [prefixWord, tailWord_2592307, baseEnd_2592307] using wordTrace_append hprefix tailTrace_2592307
  have hstable : (prefixWord ++ tailWord_2592307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592307).length < 2 ^ (prefixWord ++ tailWord_2592307).sum := by decide
  have hdescent : baseEnd_2592307 < baseStart_2592307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592365 : List Nat := [1, 5, 1, 1, 4, 2, 2, 2, 1, 4]
def baseStart_2592365 : Nat := 118140960795 + 2592365 * 2 ^ 59
def prefixEnd_2592365 : Nat := 4983230072969 + 3 ^ 40 * 2592365 * 2
def baseEnd_2592365 : Nat := 443709758964285031238479

theorem tailTrace_2592365 : CollatzResearch.WordTrace tailWord_2592365 prefixEnd_2592365 443709758964285031238479 := by
  unfold tailWord_2592365
  simp only [CollatzResearch.WordTrace]
  refine ⟨94551319253311820538722549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63034212835541213692481699 94551319253311820538722549)
  ·
    refine ⟨8864186179997983175505239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 94551319253311820538722549 8864186179997983175505239)
    ·
      refine ⟨13296279269996974763257859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8864186179997983175505239 13296279269996974763257859)
      ·
        refine ⟨19944418904995462144886789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13296279269996974763257859 19944418904995462144886789)
        ·
          refine ⟨3739578544686649152166273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19944418904995462144886789 3739578544686649152166273)
          ·
            refine ⟨2804683908514986864124705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3739578544686649152166273 2804683908514986864124705)
            ·
              refine ⟨2103512931386240148093529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2804683908514986864124705 2103512931386240148093529)
              ·
                refine ⟨1577634698539680111070147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2103512931386240148093529 1577634698539680111070147)
                ·
                  refine ⟨2366452047809520166605221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1577634698539680111070147 2366452047809520166605221)
                  ·
                    refine ⟨443709758964285031238479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2366452047809520166605221 443709758964285031238479)
                    ·
                      rfl

theorem cell23_2592365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 2, 1, 4].length) (baseStart_2592365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2592365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2592365 prefixEnd_2592365 := by exact prefixLift 2592365
  have htrace : WordTrace (prefixWord ++ tailWord_2592365) baseStart_2592365 baseEnd_2592365 := by
    simpa [prefixWord, tailWord_2592365, baseEnd_2592365] using wordTrace_append hprefix tailTrace_2592365
  have hstable : (prefixWord ++ tailWord_2592365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592365).length < 2 ^ (prefixWord ++ tailWord_2592365).sum := by decide
  have hdescent : baseEnd_2592365 < baseStart_2592365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592374 : List Nat := [5, 1, 1, 2, 2, 1, 1, 2, 3, 5]
def baseStart_2592374 : Nat := 118140960795 + 2592374 * 2 ^ 59
def prefixEnd_2592374 : Nat := 4983230072969 + 3 ^ 40 * 2592374 * 2
def baseEnd_2592374 : Nat := 443711299406248519500965

theorem tailTrace_2592374 : CollatzResearch.WordTrace tailWord_2592374 prefixEnd_2592374 443711299406248519500965 := by
  unfold tailWord_2592374
  simp only [CollatzResearch.WordTrace]
  refine ⟨5909477969392450942237511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63034431673519476717200117 5909477969392450942237511)
  ·
    refine ⟨8864216954088676413356267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5909477969392450942237511 8864216954088676413356267)
    ·
      refine ⟨13296325431133014620034401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8864216954088676413356267 13296325431133014620034401)
      ·
        refine ⟨9972244073349760965025801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13296325431133014620034401 9972244073349760965025801)
        ·
          refine ⟨7479183055012320723769351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9972244073349760965025801 7479183055012320723769351)
          ·
            refine ⟨11218774582518481085654027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7479183055012320723769351 11218774582518481085654027)
            ·
              refine ⟨16828161873777721628481041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11218774582518481085654027 16828161873777721628481041)
              ·
                refine ⟨12621121405333291221360781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16828161873777721628481041 12621121405333291221360781)
                ·
                  refine ⟨4732920526999984208010293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12621121405333291221360781 4732920526999984208010293)
                  ·
                    refine ⟨443711299406248519500965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4732920526999984208010293 443711299406248519500965)
                    ·
                      rfl

theorem cell23_2592374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_2592374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2592374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2592374 prefixEnd_2592374 := by exact prefixLift 2592374
  have htrace : WordTrace (prefixWord ++ tailWord_2592374) baseStart_2592374 baseEnd_2592374 := by
    simpa [prefixWord, tailWord_2592374, baseEnd_2592374] using wordTrace_append hprefix tailTrace_2592374
  have hstable : (prefixWord ++ tailWord_2592374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592374).length < 2 ^ (prefixWord ++ tailWord_2592374).sum := by decide
  have hdescent : baseEnd_2592374 < baseStart_2592374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592377 : List Nat := [1, 2, 1, 3, 3, 1, 1, 1, 5, 1, 4]
def baseStart_2592377 : Nat := 118140960795 + 2592377 * 2 ^ 59
def prefixEnd_2592377 : Nat := 4983230072969 + 3 ^ 40 * 2592377 * 2
def baseEnd_2592377 : Nat := 1331135438660709046765381

theorem tailTrace_2592377 : CollatzResearch.WordTrace tailWord_2592377 prefixEnd_2592377 1331135438660709046765381 := by
  unfold tailWord_2592377
  simp only [CollatzResearch.WordTrace]
  refine ⟨94551756929268346588159385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63034504619512231058772923 94551756929268346588159385)
  ·
    refine ⟨70913817696951259941119539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94551756929268346588159385 70913817696951259941119539)
    ·
      refine ⟨106370726545426889911679309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70913817696951259941119539 106370726545426889911679309)
      ·
        refine ⟨39889022454535083716879741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106370726545426889911679309 39889022454535083716879741)
        ·
          refine ⟨14958383420450656393829903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39889022454535083716879741 14958383420450656393829903)
          ·
            refine ⟨22437575130675984590744855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14958383420450656393829903 22437575130675984590744855)
            ·
              refine ⟨33656362696013976886117283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22437575130675984590744855 33656362696013976886117283)
              ·
                refine ⟨50484544044020965329175925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33656362696013976886117283 50484544044020965329175925)
                ·
                  refine ⟨4732926004126965499610243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50484544044020965329175925 4732926004126965499610243)
                  ·
                    refine ⟨7099389006190448249415365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4732926004126965499610243 7099389006190448249415365)
                    ·
                      refine ⟨1331135438660709046765381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7099389006190448249415365 1331135438660709046765381)
                      ·
                        rfl

theorem cell23_2592377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 5, 1, 4].length) (baseStart_2592377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2592377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2592377 prefixEnd_2592377 := by exact prefixLift 2592377
  have htrace : WordTrace (prefixWord ++ tailWord_2592377) baseStart_2592377 baseEnd_2592377 := by
    simpa [prefixWord, tailWord_2592377, baseEnd_2592377] using wordTrace_append hprefix tailTrace_2592377
  have hstable : (prefixWord ++ tailWord_2592377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592377).length < 2 ^ (prefixWord ++ tailWord_2592377).sum := by decide
  have hdescent : baseEnd_2592377 < baseStart_2592377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592387 : List Nat := [1, 1, 1, 3, 3, 1, 1, 2, 6, 4]
def baseStart_2592387 : Nat := 118140960795 + 2592387 * 2 ^ 59
def prefixEnd_2592387 : Nat := 4983230072969 + 3 ^ 40 * 2592387 * 2
def baseEnd_2592387 : Nat := 443713524489084669213445

theorem tailTrace_2592387 : CollatzResearch.WordTrace tailWord_2592387 prefixEnd_2592387 443713524489084669213445 := by
  unfold tailWord_2592387
  simp only [CollatzResearch.WordTrace]
  refine ⟨94552121659232118296023415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63034747772821412197348943 94552121659232118296023415)
  ·
    refine ⟨141828182488848177444035123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94552121659232118296023415 141828182488848177444035123)
    ·
      refine ⟨212742273733272266166052685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141828182488848177444035123 212742273733272266166052685)
      ·
        refine ⟨79778352649977099812269757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 212742273733272266166052685 79778352649977099812269757)
        ·
          refine ⟨29916882243741412429601159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79778352649977099812269757 29916882243741412429601159)
          ·
            refine ⟨44875323365612118644401739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29916882243741412429601159 44875323365612118644401739)
            ·
              refine ⟨67312985048418177966602609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44875323365612118644401739 67312985048418177966602609)
              ·
                refine ⟨50484738786313633474951957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67312985048418177966602609 50484738786313633474951957)
                ·
                  refine ⟨2366472130608451569138373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 50484738786313633474951957 2366472130608451569138373)
                  ·
                    refine ⟨443713524489084669213445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2366472130608451569138373 443713524489084669213445)
                    ·
                      rfl

theorem cell23_2592387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 6, 4].length) (baseStart_2592387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2592387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2592387 prefixEnd_2592387 := by exact prefixLift 2592387
  have htrace : WordTrace (prefixWord ++ tailWord_2592387) baseStart_2592387 baseEnd_2592387 := by
    simpa [prefixWord, tailWord_2592387, baseEnd_2592387] using wordTrace_append hprefix tailTrace_2592387
  have hstable : (prefixWord ++ tailWord_2592387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592387).length < 2 ^ (prefixWord ++ tailWord_2592387).sum := by decide
  have hdescent : baseEnd_2592387 < baseStart_2592387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592394 : List Nat := [3, 1, 2, 3, 2, 1, 2, 1, 3, 1, 4]
def baseStart_2592394 : Nat := 118140960795 + 2592394 * 2 ^ 59
def prefixEnd_2592394 : Nat := 4983230072969 + 3 ^ 40 * 2592394 * 2
def baseEnd_2592394 : Nat := 1331144167831835480252803

theorem tailTrace_2592394 : CollatzResearch.WordTrace tailWord_2592394 prefixEnd_2592394 1331144167831835480252803 := by
  unfold tailWord_2592394
  simp only [CollatzResearch.WordTrace]
  refine ⟨23638094242551689622882059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63034917980137838994352157 23638094242551689622882059)
  ·
    refine ⟨35457141363827534434323089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23638094242551689622882059 35457141363827534434323089)
    ·
      refine ⟨26592856022870650825742317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35457141363827534434323089 26592856022870650825742317)
      ·
        refine ⟨9972321008576494059653369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26592856022870650825742317 9972321008576494059653369)
        ·
          refine ⟨7479240756432370544740027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9972321008576494059653369 7479240756432370544740027)
          ·
            refine ⟨11218861134648555817110041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7479240756432370544740027 11218861134648555817110041)
            ·
              refine ⟨8414145850986416862832531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11218861134648555817110041 8414145850986416862832531)
              ·
                refine ⟨12621218776479625294248797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8414145850986416862832531 12621218776479625294248797)
                ·
                  refine ⟨4732957041179859485343299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12621218776479625294248797 4732957041179859485343299)
                  ·
                    refine ⟨7099435561769789228014949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4732957041179859485343299 7099435561769789228014949)
                    ·
                      refine ⟨1331144167831835480252803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7099435561769789228014949 1331144167831835480252803)
                      ·
                        rfl

theorem cell23_2592394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_2592394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2592394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2592394 prefixEnd_2592394 := by exact prefixLift 2592394
  have htrace : WordTrace (prefixWord ++ tailWord_2592394) baseStart_2592394 baseEnd_2592394 := by
    simpa [prefixWord, tailWord_2592394, baseEnd_2592394] using wordTrace_append hprefix tailTrace_2592394
  have hstable : (prefixWord ++ tailWord_2592394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592394).length < 2 ^ (prefixWord ++ tailWord_2592394).sum := by decide
  have hdescent : baseEnd_2592394 < baseStart_2592394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592398 : List Nat := [4, 1, 1, 3, 1, 4, 1, 1, 2, 3, 2]
def baseStart_2592398 : Nat := 118140960795 + 2592398 * 2 ^ 59
def prefixEnd_2592398 : Nat := 4983230072969 + 3 ^ 40 * 2592398 * 2
def baseEnd_2592398 : Nat := 1331146221754453464602785

theorem tailTrace_2592398 : CollatzResearch.WordTrace tailWord_2592398 prefixEnd_2592398 1331146221754453464602785 := by
  unfold tailWord_2592398
  simp only [CollatzResearch.WordTrace]
  refine ⟨11819065357774033396834231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63035015241461511449782565 11819065357774033396834231)
  ·
    refine ⟨17728598036661050095251347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11819065357774033396834231 17728598036661050095251347)
    ·
      refine ⟨26592897054991575142877021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17728598036661050095251347 26592897054991575142877021)
      ·
        refine ⟨9972336395621840678578883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26592897054991575142877021 9972336395621840678578883)
        ·
          refine ⟨14958504593432761017868325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9972336395621840678578883 14958504593432761017868325)
          ·
            refine ⟨2804719611268642690850311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14958504593432761017868325 2804719611268642690850311)
            ·
              refine ⟨4207079416902964036275467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2804719611268642690850311 4207079416902964036275467)
              ·
                refine ⟨6310619125354446054413201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4207079416902964036275467 6310619125354446054413201)
                ·
                  refine ⟨4732964344015834540809901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6310619125354446054413201 4732964344015834540809901)
                  ·
                    refine ⟨1774861629005937952803713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4732964344015834540809901 1774861629005937952803713)
                    ·
                      refine ⟨1331146221754453464602785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1774861629005937952803713 1331146221754453464602785)
                      ·
                        rfl

theorem cell23_2592398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_2592398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2592398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2592398 prefixEnd_2592398 := by exact prefixLift 2592398
  have htrace : WordTrace (prefixWord ++ tailWord_2592398) baseStart_2592398 baseEnd_2592398 := by
    simpa [prefixWord, tailWord_2592398, baseEnd_2592398] using wordTrace_append hprefix tailTrace_2592398
  have hstable : (prefixWord ++ tailWord_2592398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592398).length < 2 ^ (prefixWord ++ tailWord_2592398).sum := by decide
  have hdescent : baseEnd_2592398 < baseStart_2592398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592400 : List Nat := [2, 1, 1, 1, 1, 1, 3, 13]
def baseStart_2592400 : Nat := 118140960795 + 2592400 * 2 ^ 59
def prefixEnd_2592400 : Nat := 4983230072969 + 3 ^ 40 * 2592400 * 2
def baseEnd_2592400 : Nat := 49301749952435646547325

theorem tailTrace_2592400 : CollatzResearch.WordTrace tailWord_2592400 prefixEnd_2592400 49301749952435646547325 := by
  unfold tailWord_2592400
  simp only [CollatzResearch.WordTrace]
  refine ⟨47276297904092510758123327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63035063872123347677497769 47276297904092510758123327)
  ·
    refine ⟨70914446856138766137184991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47276297904092510758123327 70914446856138766137184991)
    ·
      refine ⟨106371670284208149205777487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70914446856138766137184991 106371670284208149205777487)
      ·
        refine ⟨159557505426312223808666231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106371670284208149205777487 159557505426312223808666231)
        ·
          refine ⟨239336258139468335712999347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159557505426312223808666231 239336258139468335712999347)
          ·
            refine ⟨359004387209202503569499021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239336258139468335712999347 359004387209202503569499021)
            ·
              refine ⟨134626645203450938838562133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 359004387209202503569499021 134626645203450938838562133)
              ·
                refine ⟨49301749952435646547325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 134626645203450938838562133 49301749952435646547325)
                ·
                  rfl

theorem cell23_2592400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 13].length) (baseStart_2592400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2592400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2592400 prefixEnd_2592400 := by exact prefixLift 2592400
  have htrace : WordTrace (prefixWord ++ tailWord_2592400) baseStart_2592400 baseEnd_2592400 := by
    simpa [prefixWord, tailWord_2592400, baseEnd_2592400] using wordTrace_append hprefix tailTrace_2592400
  have hstable : (prefixWord ++ tailWord_2592400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592400).length < 2 ^ (prefixWord ++ tailWord_2592400).sum := by decide
  have hdescent : baseEnd_2592400 < baseStart_2592400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592417 : List Nat := [1, 2, 3, 3, 2, 2, 10]
def baseStart_2592417 : Nat := 118140960795 + 2592417 * 2 ^ 59
def prefixEnd_2592417 : Nat := 4983230072969 + 3 ^ 40 * 2592417 * 2
def baseEnd_2592417 : Nat := 16434024418356652966237

theorem tailTrace_2592417 : CollatzResearch.WordTrace tailWord_2592417 prefixEnd_2592417 16434024418356652966237 := by
  unfold tailWord_2592417
  simp only [CollatzResearch.WordTrace]
  refine ⟨94553215849123433419615505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63035477232748955613077003 94553215849123433419615505)
  ·
    refine ⟨70914911886842575064711629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94553215849123433419615505 70914911886842575064711629)
    ·
      refine ⟨26593091957565965649266861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70914911886842575064711629 26593091957565965649266861)
      ·
        refine ⟨9972409484087237118475073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26593091957565965649266861 9972409484087237118475073)
        ·
          refine ⟨7479307113065427838856305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9972409484087237118475073 7479307113065427838856305)
          ·
            refine ⟨5609480334799070879142229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7479307113065427838856305 5609480334799070879142229)
            ·
              refine ⟨16434024418356652966237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5609480334799070879142229 16434024418356652966237)
              ·
                rfl

theorem cell23_2592417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 10].length) (baseStart_2592417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2592417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2592417 prefixEnd_2592417 := by exact prefixLift 2592417
  have htrace : WordTrace (prefixWord ++ tailWord_2592417) baseStart_2592417 baseEnd_2592417 := by
    simpa [prefixWord, tailWord_2592417, baseEnd_2592417] using wordTrace_append hprefix tailTrace_2592417
  have hstable : (prefixWord ++ tailWord_2592417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592417).length < 2 ^ (prefixWord ++ tailWord_2592417).sum := by decide
  have hdescent : baseEnd_2592417 < baseStart_2592417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592438 : List Nat := [5, 1, 3, 1, 1, 3, 1, 1, 1, 6]
def baseStart_2592438 : Nat := 118140960795 + 2592438 * 2 ^ 59
def prefixEnd_2592438 : Nat := 4983230072969 + 3 ^ 40 * 2592438 * 2
def baseEnd_2592438 : Nat := 443722253660211102700867

theorem tailTrace_2592438 : CollatzResearch.WordTrace tailWord_2592438 prefixEnd_2592438 443722253660211102700867 := by
  unfold tailWord_2592438
  simp only [CollatzResearch.WordTrace]
  refine ⟨5909623861377959625383123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63035987854698236004086645 5909623861377959625383123)
  ·
    refine ⟨8864435792066939438074685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5909623861377959625383123 8864435792066939438074685)
    ·
      refine ⟨3324163422025102289278007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8864435792066939438074685 3324163422025102289278007)
      ·
        refine ⟨4986245133037653433917011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3324163422025102289278007 4986245133037653433917011)
        ·
          refine ⟨7479367699556480150875517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4986245133037653433917011 7479367699556480150875517)
          ·
            refine ⟨2804762887333680056578319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7479367699556480150875517 2804762887333680056578319)
            ·
              refine ⟨4207144331000520084867479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2804762887333680056578319 4207144331000520084867479)
              ·
                refine ⟨6310716496500780127301219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4207144331000520084867479 6310716496500780127301219)
                ·
                  refine ⟨9466074744751170190951829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6310716496500780127301219 9466074744751170190951829)
                  ·
                    refine ⟨443722253660211102700867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9466074744751170190951829 443722253660211102700867)
                    ·
                      rfl

theorem cell23_2592438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_2592438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2592438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2592438 prefixEnd_2592438 := by exact prefixLift 2592438
  have htrace : WordTrace (prefixWord ++ tailWord_2592438) baseStart_2592438 baseEnd_2592438 := by
    simpa [prefixWord, tailWord_2592438, baseEnd_2592438] using wordTrace_append hprefix tailTrace_2592438
  have hstable : (prefixWord ++ tailWord_2592438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592438).length < 2 ^ (prefixWord ++ tailWord_2592438).sum := by decide
  have hdescent : baseEnd_2592438 < baseStart_2592438 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592471 : List Nat := [1, 1, 3, 2, 1, 3, 1, 5, 1, 3, 2]
def baseStart_2592471 : Nat := 118140960795 + 2592471 * 2 ^ 59
def prefixEnd_2592471 : Nat := 4983230072969 + 3 ^ 40 * 2592471 * 2
def baseEnd_2592471 : Nat := 1331183705842231678989949

theorem tailTrace_2592471 : CollatzResearch.WordTrace tailWord_2592471 prefixEnd_2592471 1331183705842231678989949 := by
  unfold tailWord_2592471
  simp only [CollatzResearch.WordTrace]
  refine ⟨94555185390927800642081267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63036790260618533761387511 94555185390927800642081267)
  ·
    refine ⟨141832778086391700963121901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94555185390927800642081267 141832778086391700963121901)
    ·
      refine ⟨53187291782396887861170713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141832778086391700963121901 53187291782396887861170713)
      ·
        refine ⟨39890468836797665895878035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53187291782396887861170713 39890468836797665895878035)
        ·
          refine ⟨59835703255196498843817053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39890468836797665895878035 59835703255196498843817053)
          ·
            refine ⟨22438388720698687066431395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59835703255196498843817053 22438388720698687066431395)
            ·
              refine ⟨33657583081048030599647093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22438388720698687066431395 33657583081048030599647093)
              ·
                refine ⟨3155398413848252868716915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33657583081048030599647093 3155398413848252868716915)
                ·
                  refine ⟨4733097620772379303075373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3155398413848252868716915 4733097620772379303075373)
                  ·
                    refine ⟨1774911607789642238653265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4733097620772379303075373 1774911607789642238653265)
                    ·
                      refine ⟨1331183705842231678989949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1774911607789642238653265 1331183705842231678989949)
                      ·
                        rfl

theorem cell23_2592471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 5, 1, 3, 2].length) (baseStart_2592471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2592471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2592471 prefixEnd_2592471 := by exact prefixLift 2592471
  have htrace : WordTrace (prefixWord ++ tailWord_2592471) baseStart_2592471 baseEnd_2592471 := by
    simpa [prefixWord, tailWord_2592471, baseEnd_2592471] using wordTrace_append hprefix tailTrace_2592471
  have hstable : (prefixWord ++ tailWord_2592471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592471).length < 2 ^ (prefixWord ++ tailWord_2592471).sum := by decide
  have hdescent : baseEnd_2592471 < baseStart_2592471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592535 : List Nat := [1, 1, 3, 4, 2, 2, 2, 2, 2, 2, 2]
def baseStart_2592535 : Nat := 118140960795 + 2592535 * 2 ^ 59
def prefixEnd_2592535 : Nat := 4983230072969 + 3 ^ 40 * 2592535 * 2
def baseEnd_2592535 : Nat := 1331216568604119428589655

theorem tailTrace_2592535 : CollatzResearch.WordTrace tailWord_2592535 prefixEnd_2592535 1331216568604119428589655 := by
  unfold tailWord_2592535
  simp only [CollatzResearch.WordTrace]
  refine ⟨94557519662695939572411059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63038346441797293048274039 94557519662695939572411059)
  ·
    refine ⟨141836279494043909358616589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94557519662695939572411059 141836279494043909358616589)
    ·
      refine ⟨53188604810266466009481221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141836279494043909358616589 53188604810266466009481221)
      ·
        refine ⟨9972863401924962376777729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53188604810266466009481221 9972863401924962376777729)
        ·
          refine ⟨7479647551443721782583297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9972863401924962376777729 7479647551443721782583297)
          ·
            refine ⟨5609735663582791336937473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7479647551443721782583297 5609735663582791336937473)
            ·
              refine ⟨4207301747687093502703105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5609735663582791336937473 4207301747687093502703105)
              ·
                refine ⟨3155476310765320127027329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4207301747687093502703105 3155476310765320127027329)
                ·
                  refine ⟨2366607233073990095270497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3155476310765320127027329 2366607233073990095270497)
                  ·
                    refine ⟨1774955424805492571452873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2366607233073990095270497 1774955424805492571452873)
                    ·
                      refine ⟨1331216568604119428589655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1774955424805492571452873 1331216568604119428589655)
                      ·
                        rfl

theorem cell23_2592535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_2592535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2592535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2592535 prefixEnd_2592535 := by exact prefixLift 2592535
  have htrace : WordTrace (prefixWord ++ tailWord_2592535) baseStart_2592535 baseEnd_2592535 := by
    simpa [prefixWord, tailWord_2592535, baseEnd_2592535] using wordTrace_append hprefix tailTrace_2592535
  have hstable : (prefixWord ++ tailWord_2592535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592535).length < 2 ^ (prefixWord ++ tailWord_2592535).sum := by decide
  have hdescent : baseEnd_2592535 < baseStart_2592535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592567 : List Nat := [1, 1, 3, 1, 2, 1, 2, 1, 1, 10]
def baseStart_2592567 : Nat := 118140960795 + 2592567 * 2 ^ 59
def prefixEnd_2592567 : Nat := 4983230072969 + 3 ^ 40 * 2592567 * 2
def baseEnd_2592567 : Nat := 443744333328354434463169

theorem tailTrace_2592567 : CollatzResearch.WordTrace tailWord_2592567 prefixEnd_2592567 443744333328354434463169 := by
  unfold tailWord_2592567
  simp only [CollatzResearch.WordTrace]
  refine ⟨94558686798580009037575955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63039124532386672691717303 94558686798580009037575955)
  ·
    refine ⟨141838030197870013556363933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94558686798580009037575955 141838030197870013556363933)
    ·
      refine ⟨53189261324201255083636475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141838030197870013556363933 53189261324201255083636475)
      ·
        refine ⟨79783891986301882625454713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53189261324201255083636475 79783891986301882625454713)
        ·
          refine ⟨59837918989726411969091035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79783891986301882625454713 59837918989726411969091035)
          ·
            refine ⟨89756878484589617953636553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59837918989726411969091035 89756878484589617953636553)
            ·
              refine ⟨67317658863442213465227415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89756878484589617953636553 67317658863442213465227415)
              ·
                refine ⟨100976488295163320197841123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67317658863442213465227415 100976488295163320197841123)
                ·
                  refine ⟨151464732442744980296761685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 100976488295163320197841123 151464732442744980296761685)
                  ·
                    refine ⟨443744333328354434463169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 151464732442744980296761685 443744333328354434463169)
                    ·
                      rfl

theorem cell23_2592567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 10].length) (baseStart_2592567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2592567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2592567 prefixEnd_2592567 := by exact prefixLift 2592567
  have htrace : WordTrace (prefixWord ++ tailWord_2592567) baseStart_2592567 baseEnd_2592567 := by
    simpa [prefixWord, tailWord_2592567, baseEnd_2592567] using wordTrace_append hprefix tailTrace_2592567
  have hstable : (prefixWord ++ tailWord_2592567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592567).length < 2 ^ (prefixWord ++ tailWord_2592567).sum := by decide
  have hdescent : baseEnd_2592567 < baseStart_2592567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592601 : List Nat := [1, 2, 1, 2, 2, 3, 4, 1, 3, 4]
def baseStart_2592601 : Nat := 118140960795 + 2592601 * 2 ^ 59
def prefixEnd_2592601 : Nat := 4983230072969 + 3 ^ 40 * 2592601 * 2
def baseEnd_2592601 : Nat := 443750152775772056788117

theorem tailTrace_2592601 : CollatzResearch.WordTrace tailWord_2592601 prefixEnd_2592601 443750152775772056788117 := by
  unfold tailWord_2592601
  simp only [CollatzResearch.WordTrace]
  refine ⟨94559926880456832844313657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63039951253637888562875771 94559926880456832844313657)
  ·
    refine ⟨70919945160342624633235243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94559926880456832844313657 70919945160342624633235243)
    ·
      refine ⟨106379917740513936949852865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70919945160342624633235243 106379917740513936949852865)
      ·
        refine ⟨79784938305385452712389649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106379917740513936949852865 79784938305385452712389649)
        ·
          refine ⟨59838703729039089534292237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79784938305385452712389649 59838703729039089534292237)
          ·
            refine ⟨22439513898389658575359589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59838703729039089534292237 22439513898389658575359589)
            ·
              refine ⟨4207408855948060982879923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22439513898389658575359589 4207408855948060982879923)
              ·
                refine ⟨6311113283922091474319885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4207408855948060982879923 6311113283922091474319885)
                ·
                  refine ⟨2366667481470784302869957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6311113283922091474319885 2366667481470784302869957)
                  ·
                    refine ⟨443750152775772056788117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2366667481470784302869957 443750152775772056788117)
                    ·
                      rfl

theorem cell23_2592601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 1, 3, 4].length) (baseStart_2592601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2592601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2592601 prefixEnd_2592601 := by exact prefixLift 2592601
  have htrace : WordTrace (prefixWord ++ tailWord_2592601) baseStart_2592601 baseEnd_2592601 := by
    simpa [prefixWord, tailWord_2592601, baseEnd_2592601] using wordTrace_append hprefix tailTrace_2592601
  have hstable : (prefixWord ++ tailWord_2592601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592601).length < 2 ^ (prefixWord ++ tailWord_2592601).sum := by decide
  have hdescent : baseEnd_2592601 < baseStart_2592601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592624 : List Nat := [2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 3]
def baseStart_2592624 : Nat := 118140960795 + 2592624 * 2 ^ 59
def prefixEnd_2592624 : Nat := 4983230072969 + 3 ^ 40 * 2592624 * 2
def baseEnd_2592624 : Nat := 1331262268382369580376745

theorem tailTrace_2592624 : CollatzResearch.WordTrace tailWord_2592624 prefixEnd_2592624 1331262268382369580376745 := by
  unfold tailWord_2592624
  simp only [CollatzResearch.WordTrace]
  refine ⟨47280382879686753886200463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63040510506249005181600617 47280382879686753886200463)
  ·
    refine ⟨70920574319530130829300695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47280382879686753886200463 70920574319530130829300695)
    ·
      refine ⟨106380861479295196243951043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70920574319530130829300695 106380861479295196243951043)
      ·
        refine ⟨159571292218942794365926565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106380861479295196243951043 159571292218942794365926565)
        ·
          refine ⟨29919617291051773943611231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 159571292218942794365926565 29919617291051773943611231)
          ·
            refine ⟨44879425936577660915416847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29919617291051773943611231 44879425936577660915416847)
            ·
              refine ⟨67319138904866491373125271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44879425936577660915416847 67319138904866491373125271)
              ·
                refine ⟨100978708357299737059687907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67319138904866491373125271 100978708357299737059687907)
                ·
                  refine ⟨151468062535949605589531861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 100978708357299737059687907 151468062535949605589531861)
                  ·
                    refine ⟨3550032715686318881004653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 151468062535949605589531861 3550032715686318881004653)
                    ·
                      refine ⟨1331262268382369580376745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3550032715686318881004653 1331262268382369580376745)
                      ·
                        rfl

theorem cell23_2592624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 3].length) (baseStart_2592624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2592624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2592624 prefixEnd_2592624 := by exact prefixLift 2592624
  have htrace : WordTrace (prefixWord ++ tailWord_2592624) baseStart_2592624 baseEnd_2592624 := by
    simpa [prefixWord, tailWord_2592624, baseEnd_2592624] using wordTrace_append hprefix tailTrace_2592624
  have hstable : (prefixWord ++ tailWord_2592624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592624).length < 2 ^ (prefixWord ++ tailWord_2592624).sum := by decide
  have hdescent : baseEnd_2592624 < baseStart_2592624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592681 : List Nat := [1, 2, 1, 1, 1, 1, 4, 6, 1, 1, 4]
def baseStart_2592681 : Nat := 118140960795 + 2592681 * 2 ^ 59
def prefixEnd_2592681 : Nat := 4983230072969 + 3 ^ 40 * 2592681 * 2
def baseEnd_2592681 : Nat := 1331291536779675857363983

theorem tailTrace_2592681 : CollatzResearch.WordTrace tailWord_2592681 prefixEnd_2592681 1331291536779675857363983 := by
  unfold tailWord_2592681
  simp only [CollatzResearch.WordTrace]
  refine ⟨94562844720167006507225897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63041896480111337671483931 94562844720167006507225897)
  ·
    refine ⟨70922133540125254880419423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94562844720167006507225897 70922133540125254880419423)
    ·
      refine ⟨106383200310187882320629135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70922133540125254880419423 106383200310187882320629135)
      ·
        refine ⟨159574800465281823480943703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106383200310187882320629135 159574800465281823480943703)
        ·
          refine ⟨239362200697922735221415555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159574800465281823480943703 239362200697922735221415555)
          ·
            refine ⟨359043301046884102832123333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239362200697922735221415555 359043301046884102832123333)
            ·
              refine ⟨67320618946290769281023125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 359043301046884102832123333 67320618946290769281023125)
              ·
                refine ⟨3155654013107379810047959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 67320618946290769281023125 3155654013107379810047959)
                ·
                  refine ⟨4733481019661069715071939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3155654013107379810047959 4733481019661069715071939)
                  ·
                    refine ⟨7100221529491604572607909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4733481019661069715071939 7100221529491604572607909)
                    ·
                      refine ⟨1331291536779675857363983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7100221529491604572607909 1331291536779675857363983)
                      ·
                        rfl

theorem cell23_2592681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 6, 1, 1, 4].length) (baseStart_2592681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2592681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2592681 prefixEnd_2592681 := by exact prefixLift 2592681
  have htrace : WordTrace (prefixWord ++ tailWord_2592681) baseStart_2592681 baseEnd_2592681 := by
    simpa [prefixWord, tailWord_2592681, baseEnd_2592681] using wordTrace_append hprefix tailTrace_2592681
  have hstable : (prefixWord ++ tailWord_2592681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592681).length < 2 ^ (prefixWord ++ tailWord_2592681).sum := by decide
  have hdescent : baseEnd_2592681 < baseStart_2592681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592698 : List Nat := [3, 1, 1, 1, 2, 1, 2, 1, 7, 2, 2]
def baseStart_2592698 : Nat := 118140960795 + 2592698 * 2 ^ 59
def prefixEnd_2592698 : Nat := 4983230072969 + 3 ^ 40 * 2592698 * 2
def baseEnd_2592698 : Nat := 1331300265950802290851405

theorem tailTrace_2592698 : CollatzResearch.WordTrace tailWord_2592698 prefixEnd_2592698 1331300265950802290851405 := by
  unfold tailWord_2592698
  simp only [CollatzResearch.WordTrace]
  refine ⟨23640866190276354602648687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63042309840736945607063165 23640866190276354602648687)
  ·
    refine ⟨35461299285414531903973031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23640866190276354602648687 35461299285414531903973031)
    ·
      refine ⟨53191948928121797855959547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35461299285414531903973031 53191948928121797855959547)
      ·
        refine ⟨79787923392182696783939321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53191948928121797855959547 79787923392182696783939321)
        ·
          refine ⟨59840942544137022587954491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79787923392182696783939321 59840942544137022587954491)
          ·
            refine ⟨89761413816205533881931737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59840942544137022587954491 89761413816205533881931737)
            ·
              refine ⟨67321060362154150411448803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89761413816205533881931737 67321060362154150411448803)
              ·
                refine ⟨100981590543231225617173205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67321060362154150411448803 100981590543231225617173205)
                ·
                  refine ⟨2366756028356981850402497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 100981590543231225617173205 2366756028356981850402497)
                  ·
                    refine ⟨1775067021267736387801873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2366756028356981850402497 1775067021267736387801873)
                    ·
                      refine ⟨1331300265950802290851405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1775067021267736387801873 1331300265950802290851405)
                      ·
                        rfl

theorem cell23_2592698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 7, 2, 2].length) (baseStart_2592698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2592698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2592698 prefixEnd_2592698 := by exact prefixLift 2592698
  have htrace : WordTrace (prefixWord ++ tailWord_2592698) baseStart_2592698 baseEnd_2592698 := by
    simpa [prefixWord, tailWord_2592698, baseEnd_2592698] using wordTrace_append hprefix tailTrace_2592698
  have hstable : (prefixWord ++ tailWord_2592698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592698).length < 2 ^ (prefixWord ++ tailWord_2592698).sum := by decide
  have hdescent : baseEnd_2592698 < baseStart_2592698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592749 : List Nat := [1, 5, 1, 4, 1, 2, 2, 1, 1, 1, 4]
def baseStart_2592749 : Nat := 118140960795 + 2592749 * 2 ^ 59
def prefixEnd_2592749 : Nat := 4983230072969 + 3 ^ 40 * 2592749 * 2
def baseEnd_2592749 : Nat := 1331326453464181591313671

theorem tailTrace_2592749 : CollatzResearch.WordTrace tailWord_2592749 prefixEnd_2592749 1331326453464181591313671 := by
  unfold tailWord_2592749
  simp only [CollatzResearch.WordTrace]
  refine ⟨94565324883920654120701301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63043549922613769413800867 94565324883920654120701301)
  ·
    refine ⟨8865499207867561323815747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 94565324883920654120701301 8865499207867561323815747)
    ·
      refine ⟨13298248811801341985723621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8865499207867561323815747 13298248811801341985723621)
      ·
        refine ⟨2493421652212751622323179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13298248811801341985723621 2493421652212751622323179)
        ·
          refine ⟨3740132478319127433484769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2493421652212751622323179 3740132478319127433484769)
          ·
            refine ⟨2805099358739345575113577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3740132478319127433484769 2805099358739345575113577)
            ·
              refine ⟨2103824519054509181335183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2805099358739345575113577 2103824519054509181335183)
              ·
                refine ⟨3155736778581763772002775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2103824519054509181335183 3155736778581763772002775)
                ·
                  refine ⟨4733605167872645658004163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3155736778581763772002775 4733605167872645658004163)
                  ·
                    refine ⟨7100407751808968487006245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4733605167872645658004163 7100407751808968487006245)
                    ·
                      refine ⟨1331326453464181591313671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7100407751808968487006245 1331326453464181591313671)
                      ·
                        rfl

theorem cell23_2592749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_2592749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2592749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2592749 prefixEnd_2592749 := by exact prefixLift 2592749
  have htrace : WordTrace (prefixWord ++ tailWord_2592749) baseStart_2592749 baseEnd_2592749 := by
    simpa [prefixWord, tailWord_2592749, baseEnd_2592749] using wordTrace_append hprefix tailTrace_2592749
  have hstable : (prefixWord ++ tailWord_2592749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592749).length < 2 ^ (prefixWord ++ tailWord_2592749).sum := by decide
  have hdescent : baseEnd_2592749 < baseStart_2592749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592765 : List Nat := [1, 4, 1, 1, 1, 2, 5, 2, 2, 1, 3]
def baseStart_2592765 : Nat := 118140960795 + 2592765 * 2 ^ 59
def prefixEnd_2592765 : Nat := 4983230072969 + 3 ^ 40 * 2592765 * 2
def baseEnd_2592765 : Nat := 1331334669154653528713597

theorem tailTrace_2592765 : CollatzResearch.WordTrace tailWord_2592765 prefixEnd_2592765 1331334669154653528713597 := by
  unfold tailWord_2592765
  simp only [CollatzResearch.WordTrace]
  refine ⟨94565908451862688853283749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63043938967908459235522499 94565908451862688853283749)
  ·
    refine ⟨17731107834724254159990703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94565908451862688853283749 17731107834724254159990703)
    ·
      refine ⟨26596661752086381239986055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17731107834724254159990703 26596661752086381239986055)
      ·
        refine ⟨39894992628129571859979083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26596661752086381239986055 39894992628129571859979083)
        ·
          refine ⟨59842488942194357789968625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39894992628129571859979083 59842488942194357789968625)
          ·
            refine ⟨44881866706645768342476469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59842488942194357789968625 44881866706645768342476469)
            ·
              refine ⟨4207675003748040782107169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44881866706645768342476469 4207675003748040782107169)
              ·
                refine ⟨3155756252811030586580377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4207675003748040782107169 3155756252811030586580377)
                ·
                  refine ⟨2366817189608272939935283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3155756252811030586580377 2366817189608272939935283)
                  ·
                    refine ⟨3550225784412409409902925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2366817189608272939935283 3550225784412409409902925)
                    ·
                      refine ⟨1331334669154653528713597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3550225784412409409902925 1331334669154653528713597)
                      ·
                        rfl

theorem cell23_2592765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 2, 2, 1, 3].length) (baseStart_2592765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2592765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2592765 prefixEnd_2592765 := by exact prefixLift 2592765
  have htrace : WordTrace (prefixWord ++ tailWord_2592765) baseStart_2592765 baseEnd_2592765 := by
    simpa [prefixWord, tailWord_2592765, baseEnd_2592765] using wordTrace_append hprefix tailTrace_2592765
  have hstable : (prefixWord ++ tailWord_2592765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592765).length < 2 ^ (prefixWord ++ tailWord_2592765).sum := by decide
  have hdescent : baseEnd_2592765 < baseStart_2592765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592782 : List Nat := [4, 1, 1, 2, 2, 1, 5, 1, 2, 1, 3]
def baseStart_2592782 : Nat := 118140960795 + 2592782 * 2 ^ 59
def prefixEnd_2592782 : Nat := 4983230072969 + 3 ^ 40 * 2592782 * 2
def baseEnd_2592782 : Nat := 1331343398325779962201019

theorem tailTrace_2592782 : CollatzResearch.WordTrace tailWord_2592782 prefixEnd_2592782 1331343398325779962201019 := by
  unfold tailWord_2592782
  simp only [CollatzResearch.WordTrace]
  refine ⟨11820816061600137594581575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63044352328534067171101733 11820816061600137594581575)
  ·
    refine ⟨17731224092400206391872363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11820816061600137594581575 17731224092400206391872363)
    ·
      refine ⟨26596836138600309587808545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17731224092400206391872363 26596836138600309587808545)
      ·
        refine ⟨19947627103950232190856409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26596836138600309587808545 19947627103950232190856409)
        ·
          refine ⟨14960720327962674143142307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19947627103950232190856409 14960720327962674143142307)
          ·
            refine ⟨22441080491944011214713461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14960720327962674143142307 22441080491944011214713461)
            ·
              refine ⟨2103851296119751051379387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22441080491944011214713461 2103851296119751051379387)
              ·
                refine ⟨3155776944179626577069081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2103851296119751051379387 3155776944179626577069081)
                ·
                  refine ⟨2366832708134719932801811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3155776944179626577069081 2366832708134719932801811)
                  ·
                    refine ⟨3550249062202079899202717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2366832708134719932801811 3550249062202079899202717)
                    ·
                      refine ⟨1331343398325779962201019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3550249062202079899202717 1331343398325779962201019)
                      ·
                        rfl

theorem cell23_2592782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 1, 2, 1, 3].length) (baseStart_2592782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2592782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2592782 prefixEnd_2592782 := by exact prefixLift 2592782
  have htrace : WordTrace (prefixWord ++ tailWord_2592782) baseStart_2592782 baseEnd_2592782 := by
    simpa [prefixWord, tailWord_2592782, baseEnd_2592782] using wordTrace_append hprefix tailTrace_2592782
  have hstable : (prefixWord ++ tailWord_2592782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592782).length < 2 ^ (prefixWord ++ tailWord_2592782).sum := by decide
  have hdescent : baseEnd_2592782 < baseStart_2592782 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592805 : List Nat := [1, 3, 1, 2, 2, 3, 1, 2, 4, 2, 2]
def baseStart_2592805 : Nat := 118140960795 + 2592805 * 2 ^ 59
def prefixEnd_2592805 : Nat := 4983230072969 + 3 ^ 40 * 2592805 * 2
def baseEnd_2592805 : Nat := 1331355208380833372213413

theorem tailTrace_2592805 : CollatzResearch.WordTrace tailWord_2592805 prefixEnd_2592805 1331355208380833372213413 := by
  unfold tailWord_2592805
  simp only [CollatzResearch.WordTrace]
  refine ⟨94567367371717775684739869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63044911581145183789826579 94567367371717775684739869)
  ·
    refine ⟨35462762764394165881777451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94567367371717775684739869 35462762764394165881777451)
    ·
      refine ⟨53194144146591248822666177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35462762764394165881777451 53194144146591248822666177)
      ·
        refine ⟨39895608109943436616999633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53194144146591248822666177 39895608109943436616999633)
        ·
          refine ⟨29921706082457577462749725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39895608109943436616999633 29921706082457577462749725)
          ·
            refine ⟨11220639780921591548531147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29921706082457577462749725 11220639780921591548531147)
            ·
              refine ⟨16830959671382387322796721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11220639780921591548531147 16830959671382387322796721)
              ·
                refine ⟨12623219753536790492097541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16830959671382387322796721 12623219753536790492097541)
                ·
                  refine ⟨2366853703788148217268289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12623219753536790492097541 2366853703788148217268289)
                  ·
                    refine ⟨1775140277841111162951217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2366853703788148217268289 1775140277841111162951217)
                    ·
                      refine ⟨1331355208380833372213413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1775140277841111162951217 1331355208380833372213413)
                      ·
                        rfl

theorem cell23_2592805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 4, 2, 2].length) (baseStart_2592805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2592805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2592805 prefixEnd_2592805 := by exact prefixLift 2592805
  have htrace : WordTrace (prefixWord ++ tailWord_2592805) baseStart_2592805 baseEnd_2592805 := by
    simpa [prefixWord, tailWord_2592805, baseEnd_2592805] using wordTrace_append hprefix tailTrace_2592805
  have hstable : (prefixWord ++ tailWord_2592805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592805).length < 2 ^ (prefixWord ++ tailWord_2592805).sum := by decide
  have hdescent : baseEnd_2592805 < baseStart_2592805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592822 : List Nat := [5, 1, 2, 1, 1, 1, 1, 3, 4, 2, 2]
def baseStart_2592822 : Nat := 118140960795 + 2592822 * 2 ^ 59
def prefixEnd_2592822 : Nat := 4983230072969 + 3 ^ 40 * 2592822 * 2
def baseEnd_2592822 : Nat := 1331363937551959805700835

theorem tailTrace_2592822 : CollatzResearch.WordTrace tailWord_2592822 prefixEnd_2592822 1331363937551959805700835 := by
  unfold tailWord_2592822
  simp only [CollatzResearch.WordTrace]
  refine ⟨5910499213291011724256795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63045324941770791725405813 5910499213291011724256795)
  ·
    refine ⟨8865748819936517586385193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5910499213291011724256795 8865748819936517586385193)
    ·
      refine ⟨6649311614952388189788895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8865748819936517586385193 6649311614952388189788895)
      ·
        refine ⟨9973967422428582284683343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6649311614952388189788895 9973967422428582284683343)
        ·
          refine ⟨14960951133642873427025015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9973967422428582284683343 14960951133642873427025015)
          ·
            refine ⟨22441426700464310140537523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14960951133642873427025015 22441426700464310140537523)
            ·
              refine ⟨33662140050696465210806285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22441426700464310140537523 33662140050696465210806285)
              ·
                refine ⟨12623302519011174454052357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33662140050696465210806285 12623302519011174454052357)
                ·
                  refine ⟨2366869222314595210134817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12623302519011174454052357 2366869222314595210134817)
                  ·
                    refine ⟨1775151916735946407601113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2366869222314595210134817 1775151916735946407601113)
                    ·
                      refine ⟨1331363937551959805700835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1775151916735946407601113 1331363937551959805700835)
                      ·
                        rfl

theorem cell23_2592822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_2592822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2592822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2592822 prefixEnd_2592822 := by exact prefixLift 2592822
  have htrace : WordTrace (prefixWord ++ tailWord_2592822) baseStart_2592822 baseEnd_2592822 := by
    simpa [prefixWord, tailWord_2592822, baseEnd_2592822] using wordTrace_append hprefix tailTrace_2592822
  have hstable : (prefixWord ++ tailWord_2592822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592822).length < 2 ^ (prefixWord ++ tailWord_2592822).sum := by decide
  have hdescent : baseEnd_2592822 < baseStart_2592822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592841 : List Nat := [1, 2, 1, 1, 2, 2, 3, 2, 4, 5]
def baseStart_2592841 : Nat := 118140960795 + 2592841 * 2 ^ 59
def prefixEnd_2592841 : Nat := 4983230072969 + 3 ^ 40 * 2592841 * 2
def baseEnd_2592841 : Nat := 443791231228131743787749

theorem tailTrace_2592841 : CollatzResearch.WordTrace tailWord_2592841 prefixEnd_2592841 443791231228131743787749 := by
  unfold tailWord_2592841
  simp only [CollatzResearch.WordTrace]
  refine ⟨94568680399587353833050377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63045786933058235888700251 94568680399587353833050377)
  ·
    refine ⟨70926510299690515374787783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94568680399587353833050377 70926510299690515374787783)
    ·
      refine ⟨106389765449535773062181675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70926510299690515374787783 106389765449535773062181675)
      ·
        refine ⟨159584648174303659593272513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106389765449535773062181675 159584648174303659593272513)
        ·
          refine ⟨119688486130727744694954385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159584648174303659593272513 119688486130727744694954385)
          ·
            refine ⟨89766364598045808521215789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119688486130727744694954385 89766364598045808521215789)
            ·
              refine ⟨33662386724267178195455921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89766364598045808521215789 33662386724267178195455921)
              ·
                refine ⟨25246790043200383646591941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33662386724267178195455921 25246790043200383646591941)
                ·
                  refine ⟨4733773133100071933735989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25246790043200383646591941 4733773133100071933735989)
                  ·
                    refine ⟨443791231228131743787749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4733773133100071933735989 443791231228131743787749)
                    ·
                      rfl

theorem cell23_2592841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 4, 5].length) (baseStart_2592841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2592841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2592841 prefixEnd_2592841 := by exact prefixLift 2592841
  have htrace : WordTrace (prefixWord ++ tailWord_2592841) baseStart_2592841 baseEnd_2592841 := by
    simpa [prefixWord, tailWord_2592841, baseEnd_2592841] using wordTrace_append hprefix tailTrace_2592841
  have hstable : (prefixWord ++ tailWord_2592841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592841).length < 2 ^ (prefixWord ++ tailWord_2592841).sum := by decide
  have hdescent : baseEnd_2592841 < baseStart_2592841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592858 : List Nat := [3, 1, 1, 2, 1, 1, 6, 1, 2, 5]
def baseStart_2592858 : Nat := 118140960795 + 2592858 * 2 ^ 59
def prefixEnd_2592858 : Nat := 4983230072969 + 3 ^ 40 * 2592858 * 2
def baseEnd_2592858 : Nat := 443794140951840554950223

theorem tailTrace_2592858 : CollatzResearch.WordTrace tailWord_2592858 prefixEnd_2592858 443794140951840554950223 := by
  unfold tailWord_2592858
  simp only [CollatzResearch.WordTrace]
  refine ⟨23642325110131441434104807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63046200293683843824279485 23642325110131441434104807)
  ·
    refine ⟨35463487665197162151157211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23642325110131441434104807 35463487665197162151157211)
    ·
      refine ⟨53195231497795743226735817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35463487665197162151157211 53195231497795743226735817)
      ·
        refine ⟨39896423623346807420051863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53195231497795743226735817 39896423623346807420051863)
        ·
          refine ⟨59844635435020211130077795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39896423623346807420051863 59844635435020211130077795)
          ·
            refine ⟨89766953152530316695116693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59844635435020211130077795 89766953152530316695116693)
            ·
              refine ⟨4207825929024858595083595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 89766953152530316695116693 4207825929024858595083595)
              ·
                refine ⟨6311738893537287892625393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4207825929024858595083595 6311738893537287892625393)
                ·
                  refine ⟨4733804170152965919469045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6311738893537287892625393 4733804170152965919469045)
                  ·
                    refine ⟨443794140951840554950223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4733804170152965919469045 443794140951840554950223)
                    ·
                      rfl

theorem cell23_2592858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 1, 2, 5].length) (baseStart_2592858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2592858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2592858 prefixEnd_2592858 := by exact prefixLift 2592858
  have htrace : WordTrace (prefixWord ++ tailWord_2592858) baseStart_2592858 baseEnd_2592858 := by
    simpa [prefixWord, tailWord_2592858, baseEnd_2592858] using wordTrace_append hprefix tailTrace_2592858
  have hstable : (prefixWord ++ tailWord_2592858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592858).length < 2 ^ (prefixWord ++ tailWord_2592858).sum := by decide
  have hdescent : baseEnd_2592858 < baseStart_2592858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592881 : List Nat := [1, 2, 2, 2, 1, 1, 3, 1, 2, 3, 5]
def baseStart_2592881 : Nat := 118140960795 + 2592881 * 2 ^ 59
def prefixEnd_2592881 : Nat := 4983230072969 + 3 ^ 40 * 2592881 * 2
def baseEnd_2592881 : Nat := 1331394232910575074863063

theorem tailTrace_2592881 : CollatzResearch.WordTrace tailWord_2592881 prefixEnd_2592881 1331394232910575074863063 := by
  unfold tailWord_2592881
  simp only [CollatzResearch.WordTrace]
  refine ⟨94570139319442440664506497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63046759546294960443004331 94570139319442440664506497)
  ·
    refine ⟨70927604489581830498379873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94570139319442440664506497 70927604489581830498379873)
    ·
      refine ⟨53195703367186372873784905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70927604489581830498379873 53195703367186372873784905)
      ·
        refine ⟨39896777525389779655338679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53195703367186372873784905 39896777525389779655338679)
        ·
          refine ⟨59845166288084669483008019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39896777525389779655338679 59845166288084669483008019)
          ·
            refine ⟨89767749432127004224512029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59845166288084669483008019 89767749432127004224512029)
            ·
              refine ⟨33662906037047626584192011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89767749432127004224512029 33662906037047626584192011)
              ·
                refine ⟨50494359055571439876288017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33662906037047626584192011 50494359055571439876288017)
                ·
                  refine ⟨37870769291678579907216013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50494359055571439876288017 37870769291678579907216013)
                  ·
                    refine ⟨14201538484379467465206005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37870769291678579907216013 14201538484379467465206005)
                    ·
                      refine ⟨1331394232910575074863063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14201538484379467465206005 1331394232910575074863063)
                      ·
                        rfl

theorem cell23_2592881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_2592881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2592881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2592881 prefixEnd_2592881 := by exact prefixLift 2592881
  have htrace : WordTrace (prefixWord ++ tailWord_2592881) baseStart_2592881 baseEnd_2592881 := by
    simpa [prefixWord, tailWord_2592881, baseEnd_2592881] using wordTrace_append hprefix tailTrace_2592881
  have hstable : (prefixWord ++ tailWord_2592881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592881).length < 2 ^ (prefixWord ++ tailWord_2592881).sum := by decide
  have hdescent : baseEnd_2592881 < baseStart_2592881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592888 : List Nat := [2, 1, 2, 1, 1, 1, 3, 5, 3, 4]
def baseStart_2592888 : Nat := 118140960795 + 2592888 * 2 ^ 59
def prefixEnd_2592888 : Nat := 4983230072969 + 3 ^ 40 * 2592888 * 2
def baseEnd_2592888 : Nat := 443799275758385515825177

theorem tailTrace_2592888 : CollatzResearch.WordTrace tailWord_2592888 prefixEnd_2592888 443799275758385515825177 := by
  unfold tailWord_2592888
  simp only [CollatzResearch.WordTrace]
  refine ⟨47285197315208540430005659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63046929753611387240007545 47285197315208540430005659)
  ·
    refine ⟨70927795972812810645008489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47285197315208540430005659 70927795972812810645008489)
    ·
      refine ⟨53195846979609607983756367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70927795972812810645008489 53195846979609607983756367)
      ·
        refine ⟨79793770469414411975634551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53195846979609607983756367 79793770469414411975634551)
        ·
          refine ⟨119690655704121617963451827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79793770469414411975634551 119690655704121617963451827)
          ·
            refine ⟨179535983556182426945177741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119690655704121617963451827 179535983556182426945177741)
            ·
              refine ⟨67325993833568410104441653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 179535983556182426945177741 67325993833568410104441653)
              ·
                refine ⟨6311811921897038447291405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67325993833568410104441653 6311811921897038447291405)
                ·
                  refine ⟨2366929470711389417734277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6311811921897038447291405 2366929470711389417734277)
                  ·
                    refine ⟨443799275758385515825177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2366929470711389417734277 443799275758385515825177)
                    ·
                      rfl

theorem cell23_2592888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5, 3, 4].length) (baseStart_2592888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2592888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2592888 prefixEnd_2592888 := by exact prefixLift 2592888
  have htrace : WordTrace (prefixWord ++ tailWord_2592888) baseStart_2592888 baseEnd_2592888 := by
    simpa [prefixWord, tailWord_2592888, baseEnd_2592888] using wordTrace_append hprefix tailTrace_2592888
  have hstable : (prefixWord ++ tailWord_2592888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592888).length < 2 ^ (prefixWord ++ tailWord_2592888).sum := by decide
  have hdescent : baseEnd_2592888 < baseStart_2592888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592891 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 4, 4, 4]
def baseStart_2592891 : Nat := 118140960795 + 2592891 * 2 ^ 59
def prefixEnd_2592891 : Nat := 4983230072969 + 3 ^ 40 * 2592891 * 2
def baseEnd_2592891 : Nat := 1331399367717120035738017

theorem tailTrace_2592891 : CollatzResearch.WordTrace tailWord_2592891 prefixEnd_2592891 1331399367717120035738017 := by
  unfold tailWord_2592891
  simp only [CollatzResearch.WordTrace]
  refine ⟨94570504049406212372370527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63047002699604141581580351 94570504049406212372370527)
  ·
    refine ⟨141855756074109318558555791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94570504049406212372370527 141855756074109318558555791)
    ·
      refine ⟨212783634111163977837833687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141855756074109318558555791 212783634111163977837833687)
      ·
        refine ⟨319175451166745966756750531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212783634111163977837833687 319175451166745966756750531)
        ·
          refine ⟨478763176750118950135125797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319175451166745966756750531 478763176750118950135125797)
          ·
            refine ⟨89768095640647303150336087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 478763176750118950135125797 89768095640647303150336087)
            ·
              refine ⟨134652143460970954725504131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89768095640647303150336087 134652143460970954725504131)
              ·
                refine ⟨201978215191456432088256197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134652143460970954725504131 201978215191456432088256197)
                ·
                  refine ⟨37870915348398081016548037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 201978215191456432088256197 37870915348398081016548037)
                  ·
                    refine ⟨7100796627824640190602757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37870915348398081016548037 7100796627824640190602757)
                    ·
                      refine ⟨1331399367717120035738017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7100796627824640190602757 1331399367717120035738017)
                      ·
                        rfl

theorem cell23_2592891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 4, 4].length) (baseStart_2592891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2592891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2592891 prefixEnd_2592891 := by exact prefixLift 2592891
  have htrace : WordTrace (prefixWord ++ tailWord_2592891) baseStart_2592891 baseEnd_2592891 := by
    simpa [prefixWord, tailWord_2592891, baseEnd_2592891] using wordTrace_append hprefix tailTrace_2592891
  have hstable : (prefixWord ++ tailWord_2592891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592891).length < 2 ^ (prefixWord ++ tailWord_2592891).sum := by decide
  have hdescent : baseEnd_2592891 < baseStart_2592891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592921 : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 6]
def baseStart_2592921 : Nat := 118140960795 + 2592921 * 2 ^ 59
def prefixEnd_2592921 : Nat := 4983230072969 + 3 ^ 40 * 2592921 * 2
def baseEnd_2592921 : Nat := 1331414772136754918362879

theorem tailTrace_2592921 : CollatzResearch.WordTrace tailWord_2592921 prefixEnd_2592921 1331414772136754918362879 := by
  unfold tailWord_2592921
  simp only [CollatzResearch.WordTrace]
  refine ⟨94571598239297527495962617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63047732159531684997308411 94571598239297527495962617)
  ·
    refine ⟨70928698679473145621971963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94571598239297527495962617 70928698679473145621971963)
    ·
      refine ⟨106393048019209718432957945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70928698679473145621971963 106393048019209718432957945)
      ·
        refine ⟨79794786014407288824718459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106393048019209718432957945 79794786014407288824718459)
        ·
          refine ⟨119692179021610933237077689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79794786014407288824718459 119692179021610933237077689)
          ·
            refine ⟨89769134266208199927808267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119692179021610933237077689 89769134266208199927808267)
            ·
              refine ⟨134653701399312299891712401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89769134266208199927808267 134653701399312299891712401)
              ·
                refine ⟨100990276049484224918784301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134653701399312299891712401 100990276049484224918784301)
                ·
                  refine ⟨37871353518556584344544113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100990276049484224918784301 37871353518556584344544113)
                  ·
                    refine ⟨28403515138917438258408085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37871353518556584344544113 28403515138917438258408085)
                    ·
                      refine ⟨1331414772136754918362879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28403515138917438258408085 1331414772136754918362879)
                      ·
                        rfl

theorem cell23_2592921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 6].length) (baseStart_2592921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2592921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2592921 prefixEnd_2592921 := by exact prefixLift 2592921
  have htrace : WordTrace (prefixWord ++ tailWord_2592921) baseStart_2592921 baseEnd_2592921 := by
    simpa [prefixWord, tailWord_2592921, baseEnd_2592921] using wordTrace_append hprefix tailTrace_2592921
  have hstable : (prefixWord ++ tailWord_2592921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592921).length < 2 ^ (prefixWord ++ tailWord_2592921).sum := by decide
  have hdescent : baseEnd_2592921 < baseStart_2592921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592935 : List Nat := [1, 1, 6, 2, 2, 1, 1, 1, 8]
def baseStart_2592935 : Nat := 118140960795 + 2592935 * 2 ^ 59
def prefixEnd_2592935 : Nat := 4983230072969 + 3 ^ 40 * 2592935 * 2
def baseEnd_2592935 : Nat := 147935773429546429287535

theorem tailTrace_2592935 : CollatzResearch.WordTrace tailWord_2592935 prefixEnd_2592935 147935773429546429287535 := by
  unfold tailWord_2592935
  simp only [CollatzResearch.WordTrace]
  refine ⟨94572108861246807886972259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63048072574164538591314839 94572108861246807886972259)
  ·
    refine ⟨141858163291870211830458389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94572108861246807886972259 141858163291870211830458389)
    ·
      refine ⟨6649601404306416179552737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 141858163291870211830458389 6649601404306416179552737)
      ·
        refine ⟨4987201053229812134664553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6649601404306416179552737 4987201053229812134664553)
        ·
          refine ⟨3740400789922359100998415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4987201053229812134664553 3740400789922359100998415)
          ·
            refine ⟨5610601184883538651497623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3740400789922359100998415 5610601184883538651497623)
            ·
              refine ⟨8415901777325307977246435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5610601184883538651497623 8415901777325307977246435)
              ·
                refine ⟨12623852665987961965869653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8415901777325307977246435 12623852665987961965869653)
                ·
                  refine ⟨147935773429546429287535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12623852665987961965869653 147935773429546429287535)
                  ·
                    rfl

theorem cell23_2592935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 8].length) (baseStart_2592935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2592935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2592935 prefixEnd_2592935 := by exact prefixLift 2592935
  have htrace : WordTrace (prefixWord ++ tailWord_2592935) baseStart_2592935 baseEnd_2592935 := by
    simpa [prefixWord, tailWord_2592935, baseEnd_2592935] using wordTrace_append hprefix tailTrace_2592935
  have hstable : (prefixWord ++ tailWord_2592935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592935).length < 2 ^ (prefixWord ++ tailWord_2592935).sum := by decide
  have hdescent : baseEnd_2592935 < baseStart_2592935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592985 : List Nat := [1, 2, 1, 2, 3, 1, 4, 3, 1, 1, 4]
def baseStart_2592985 : Nat := 118140960795 + 2592985 * 2 ^ 59
def prefixEnd_2592985 : Nat := 4983230072969 + 3 ^ 40 * 2592985 * 2
def baseEnd_2592985 : Nat := 1331447634898642667962585

theorem tailTrace_2592985 : CollatzResearch.WordTrace tailWord_2592985 prefixEnd_2592985 1331447634898642667962585 := by
  unfold tailWord_2592985
  simp only [CollatzResearch.WordTrace]
  refine ⟨94573932511065666426292409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63049288340710444284194939 94573932511065666426292409)
  ·
    refine ⟨70930449383299249819719307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94573932511065666426292409 70930449383299249819719307)
    ·
      refine ⟨106395674074948874729578961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70930449383299249819719307 106395674074948874729578961)
      ·
        refine ⟨79796755556211656047184221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106395674074948874729578961 79796755556211656047184221)
        ·
          refine ⟨29923783333579371017694083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79796755556211656047184221 29923783333579371017694083)
          ·
            refine ⟨44885675000369056526541125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29923783333579371017694083 44885675000369056526541125)
            ·
              refine ⟨8416064062569198098726461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44885675000369056526541125 8416064062569198098726461)
              ·
                refine ⟨3156024023463449287022423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8416064062569198098726461 3156024023463449287022423)
                ·
                  refine ⟨4734036035195173930533635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3156024023463449287022423 4734036035195173930533635)
                  ·
                    refine ⟨7101054052792760895800453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4734036035195173930533635 7101054052792760895800453)
                    ·
                      refine ⟨1331447634898642667962585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7101054052792760895800453 1331447634898642667962585)
                      ·
                        rfl

theorem cell23_2592985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 3, 1, 1, 4].length) (baseStart_2592985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2592985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2592985 prefixEnd_2592985 := by exact prefixLift 2592985
  have htrace : WordTrace (prefixWord ++ tailWord_2592985) baseStart_2592985 baseEnd_2592985 := by
    simpa [prefixWord, tailWord_2592985, baseEnd_2592985] using wordTrace_append hprefix tailTrace_2592985
  have hstable : (prefixWord ++ tailWord_2592985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592985).length < 2 ^ (prefixWord ++ tailWord_2592985).sum := by decide
  have hdescent : baseEnd_2592985 < baseStart_2592985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2592989 : List Nat := [1, 4, 3, 2, 1, 2, 1, 2, 2, 3, 2]
def baseStart_2592989 : Nat := 118140960795 + 2592989 * 2 ^ 59
def prefixEnd_2592989 : Nat := 4983230072969 + 3 ^ 40 * 2592989 * 2
def baseEnd_2592989 : Nat := 1331449688821260652312567

theorem tailTrace_2592989 : CollatzResearch.WordTrace tailWord_2592989 prefixEnd_2592989 1331449688821260652312567 := by
  unfold tailWord_2592989
  simp only [CollatzResearch.WordTrace]
  refine ⟨94574078403051175109438021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63049385602034116739625347 94574078403051175109438021)
  ·
    refine ⟨17732639700572095333019629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94574078403051175109438021 17732639700572095333019629)
    ·
      refine ⟨6649739887714535749882361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17732639700572095333019629 6649739887714535749882361)
      ·
        refine ⟨4987304915785901812411771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6649739887714535749882361 4987304915785901812411771)
        ·
          refine ⟨7480957373678852718617657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4987304915785901812411771 7480957373678852718617657)
          ·
            refine ⟨5610718030259139538963243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7480957373678852718617657 5610718030259139538963243)
            ·
              refine ⟨8416077045388709308444865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5610718030259139538963243 8416077045388709308444865)
              ·
                refine ⟨6312057784041531981333649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8416077045388709308444865 6312057784041531981333649)
                ·
                  refine ⟨4734043338031148986000237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6312057784041531981333649 4734043338031148986000237)
                  ·
                    refine ⟨1775266251761680869750089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4734043338031148986000237 1775266251761680869750089)
                    ·
                      refine ⟨1331449688821260652312567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1775266251761680869750089 1331449688821260652312567)
                      ·
                        rfl

theorem cell23_2592989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_2592989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2592989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2592989 prefixEnd_2592989 := by exact prefixLift 2592989
  have htrace : WordTrace (prefixWord ++ tailWord_2592989) baseStart_2592989 baseEnd_2592989 := by
    simpa [prefixWord, tailWord_2592989, baseEnd_2592989] using wordTrace_append hprefix tailTrace_2592989
  have hstable : (prefixWord ++ tailWord_2592989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2592989).length < 2 ^ (prefixWord ++ tailWord_2592989).sum := by decide
  have hdescent : baseEnd_2592989 < baseStart_2592989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2592989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593022 : List Nat := [4, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3]
def baseStart_2593022 : Nat := 118140960795 + 2593022 * 2 ^ 59
def prefixEnd_2593022 : Nat := 4983230072969 + 3 ^ 40 * 2593022 * 2
def baseEnd_2593022 : Nat := 1331466633682859023199915

theorem tailTrace_2593022 : CollatzResearch.WordTrace tailWord_2593022 prefixEnd_2593022 1331466633682859023199915 := by
  unfold tailWord_2593022
  simp only [CollatzResearch.WordTrace]
  refine ⟨11821910251491452718173665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63050188007954414496926213 11821910251491452718173665)
  ·
    refine ⟨8866432688618589538630249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11821910251491452718173665 8866432688618589538630249)
    ·
      refine ⟨6649824516463942153972687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8866432688618589538630249 6649824516463942153972687)
      ·
        refine ⟨9974736774695913230959031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6649824516463942153972687 9974736774695913230959031)
        ·
          refine ⟨14962105162043869846438547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9974736774695913230959031 14962105162043869846438547)
          ·
            refine ⟨22443157743065804769657821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14962105162043869846438547 22443157743065804769657821)
            ·
              refine ⟨8416184153649676788621683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22443157743065804769657821 8416184153649676788621683)
              ·
                refine ⟨12624276230474515182932525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8416184153649676788621683 12624276230474515182932525)
                ·
                  refine ⟨4734103586427943193599697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12624276230474515182932525 4734103586427943193599697)
                  ·
                    refine ⟨3550577689820957395199773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4734103586427943193599697 3550577689820957395199773)
                    ·
                      refine ⟨1331466633682859023199915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3550577689820957395199773 1331466633682859023199915)
                      ·
                        rfl

theorem cell23_2593022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_2593022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2593022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2593022 prefixEnd_2593022 := by exact prefixLift 2593022
  have htrace : WordTrace (prefixWord ++ tailWord_2593022) baseStart_2593022 baseEnd_2593022 := by
    simpa [prefixWord, tailWord_2593022, baseEnd_2593022] using wordTrace_append hprefix tailTrace_2593022
  have hstable : (prefixWord ++ tailWord_2593022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593022).length < 2 ^ (prefixWord ++ tailWord_2593022).sum := by decide
  have hdescent : baseEnd_2593022 < baseStart_2593022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593035 : List Nat := [1, 1, 1, 1, 5, 2, 3, 2, 1, 3, 3]
def baseStart_2593035 : Nat := 118140960795 + 2593035 * 2 ^ 59
def prefixEnd_2593035 : Nat := 4983230072969 + 3 ^ 40 * 2593035 * 2
def baseEnd_2593035 : Nat := 1331473308931367472337355

theorem tailTrace_2593035 : CollatzResearch.WordTrace tailWord_2593035 prefixEnd_2593035 1331473308931367472337355 := by
  unfold tailWord_2593035
  simp only [CollatzResearch.WordTrace]
  refine ⟨94575756160884524965612559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63050504107256349977075039 94575756160884524965612559)
  ·
    refine ⟨141863634241326787448418839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94575756160884524965612559 141863634241326787448418839)
    ·
      refine ⟨212795451361990181172628259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141863634241326787448418839 212795451361990181172628259)
      ·
        refine ⟨319193177042985271758942389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212795451361990181172628259 319193177042985271758942389)
        ·
          refine ⟨29924360347779869227400849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 319193177042985271758942389 29924360347779869227400849)
          ·
            refine ⟨22443270260834901920550637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29924360347779869227400849 22443270260834901920550637)
            ·
              refine ⟨8416226347813088220206489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22443270260834901920550637 8416226347813088220206489)
              ·
                refine ⟨6312169760859816165154867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8416226347813088220206489 6312169760859816165154867)
                ·
                  refine ⟨9468254641289724247732301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6312169760859816165154867 9468254641289724247732301)
                  ·
                    refine ⟨3550595490483646592899613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9468254641289724247732301 3550595490483646592899613)
                    ·
                      refine ⟨1331473308931367472337355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3550595490483646592899613 1331473308931367472337355)
                      ·
                        rfl

theorem cell23_2593035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2, 1, 3, 3].length) (baseStart_2593035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2593035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2593035 prefixEnd_2593035 := by exact prefixLift 2593035
  have htrace : WordTrace (prefixWord ++ tailWord_2593035) baseStart_2593035 baseEnd_2593035 := by
    simpa [prefixWord, tailWord_2593035, baseEnd_2593035] using wordTrace_append hprefix tailTrace_2593035
  have hstable : (prefixWord ++ tailWord_2593035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593035).length < 2 ^ (prefixWord ++ tailWord_2593035).sum := by decide
  have hdescent : baseEnd_2593035 < baseStart_2593035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593053 : List Nat := [1, 4, 2, 3, 2, 1, 1, 4, 1, 2, 2]
def baseStart_2593053 : Nat := 118140960795 + 2593053 * 2 ^ 59
def prefixEnd_2593053 : Nat := 4983230072969 + 3 ^ 40 * 2593053 * 2
def baseEnd_2593053 : Nat := 1331482551583148401912273

theorem tailTrace_2593053 : CollatzResearch.WordTrace tailWord_2593053 prefixEnd_2593053 1331482551583148401912273 := by
  unfold tailWord_2593053
  simp only [CollatzResearch.WordTrace]
  refine ⟨94576412674819314039767813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63050941783212876026511875 94576412674819314039767813)
  ·
    refine ⟨17733077376528621382456465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94576412674819314039767813 17733077376528621382456465)
    ·
      refine ⟨13299808032396466036842349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17733077376528621382456465 13299808032396466036842349)
      ·
        refine ⟨4987428012148674763815881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13299808032396466036842349 4987428012148674763815881)
        ·
          refine ⟨3740571009111506072861911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4987428012148674763815881 3740571009111506072861911)
          ·
            refine ⟨5610856513667259109292867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3740571009111506072861911 5610856513667259109292867)
            ·
              refine ⟨8416284770500888663939301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5610856513667259109292867 8416284770500888663939301)
              ·
                refine ⟨1578053394468916624488619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8416284770500888663939301 1578053394468916624488619)
                ·
                  refine ⟨2367080091703374936732929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1578053394468916624488619 2367080091703374936732929)
                  ·
                    refine ⟨1775310068777531202549697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2367080091703374936732929 1775310068777531202549697)
                    ·
                      refine ⟨1331482551583148401912273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1775310068777531202549697 1331482551583148401912273)
                      ·
                        rfl

theorem cell23_2593053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_2593053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2593053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2593053 prefixEnd_2593053 := by exact prefixLift 2593053
  have htrace : WordTrace (prefixWord ++ tailWord_2593053) baseStart_2593053 baseEnd_2593053 := by
    simpa [prefixWord, tailWord_2593053, baseEnd_2593053] using wordTrace_append hprefix tailTrace_2593053
  have hstable : (prefixWord ++ tailWord_2593053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593053).length < 2 ^ (prefixWord ++ tailWord_2593053).sum := by decide
  have hdescent : baseEnd_2593053 < baseStart_2593053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593068 : List Nat := [2, 2, 1, 1, 1, 3, 3, 1, 1, 8]
def baseStart_2593068 : Nat := 118140960795 + 2593068 * 2 ^ 59
def prefixEnd_2593068 : Nat := 4983230072969 + 3 ^ 40 * 2593068 * 2
def baseEnd_2593068 : Nat := 443830084597655281074901

theorem tailTrace_2593068 : CollatzResearch.WordTrace tailWord_2593068 prefixEnd_2593068 443830084597655281074901 := by
  unfold tailWord_2593068
  simp only [CollatzResearch.WordTrace]
  refine ⟨47288479884882485800781929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63051306513176647734375905 47288479884882485800781929)
  ·
    refine ⟨35466359913661864350586447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47288479884882485800781929 35466359913661864350586447)
    ·
      refine ⟨53199539870492796525879671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35466359913661864350586447 53199539870492796525879671)
      ·
        refine ⟨79799309805739194788819507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53199539870492796525879671 79799309805739194788819507)
        ·
          refine ⟨119698964708608792183229261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79799309805739194788819507 119698964708608792183229261)
          ·
            refine ⟨44887111765728297068710973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119698964708608792183229261 44887111765728297068710973)
            ·
              refine ⟨16832666912148111400766615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44887111765728297068710973 16832666912148111400766615)
              ·
                refine ⟨25249000368222167101149923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16832666912148111400766615 25249000368222167101149923)
                ·
                  refine ⟨37873500552333250651724885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25249000368222167101149923 37873500552333250651724885)
                  ·
                    refine ⟨443830084597655281074901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 37873500552333250651724885 443830084597655281074901)
                    ·
                      rfl

theorem cell23_2593068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 8].length) (baseStart_2593068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2593068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2593068 prefixEnd_2593068 := by exact prefixLift 2593068
  have htrace : WordTrace (prefixWord ++ tailWord_2593068) baseStart_2593068 baseEnd_2593068 := by
    simpa [prefixWord, tailWord_2593068, baseEnd_2593068] using wordTrace_append hprefix tailTrace_2593068
  have hstable : (prefixWord ++ tailWord_2593068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593068).length < 2 ^ (prefixWord ++ tailWord_2593068).sum := by decide
  have hdescent : baseEnd_2593068 < baseStart_2593068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593105 : List Nat := [1, 2, 2, 1, 4, 2, 1, 2, 2, 2, 4]
def baseStart_2593105 : Nat := 118140960795 + 2593105 * 2 ^ 59
def prefixEnd_2593105 : Nat := 4983230072969 + 3 ^ 40 * 2593105 * 2
def baseEnd_2593105 : Nat := 1331509252577182198462033

theorem tailTrace_2593105 : CollatzResearch.WordTrace tailWord_2593105 prefixEnd_2593105 1331509252577182198462033 := by
  unfold tailWord_2593105
  simp only [CollatzResearch.WordTrace]
  refine ⟨94578309270630926920660769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63052206180420617947107179 94578309270630926920660769)
  ·
    refine ⟨70933731952973195190495577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94578309270630926920660769 70933731952973195190495577)
    ·
      refine ⟨53200298964729896392871683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70933731952973195190495577 53200298964729896392871683)
      ·
        refine ⟨79800448447094844589307525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53200298964729896392871683 79800448447094844589307525)
        ·
          refine ⟨14962584083830283360495161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79800448447094844589307525 14962584083830283360495161)
          ·
            refine ⟨11221938062872712520371371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14962584083830283360495161 11221938062872712520371371)
            ·
              refine ⟨16832907094309068780557057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11221938062872712520371371 16832907094309068780557057)
              ·
                refine ⟨12624680320731801585417793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16832907094309068780557057 12624680320731801585417793)
                ·
                  refine ⟨9468510240548851189063345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12624680320731801585417793 9468510240548851189063345)
                  ·
                    refine ⟨7101382680411638391797509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9468510240548851189063345 7101382680411638391797509)
                    ·
                      refine ⟨1331509252577182198462033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7101382680411638391797509 1331509252577182198462033)
                      ·
                        rfl

theorem cell23_2593105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2, 2, 4].length) (baseStart_2593105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2593105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2593105 prefixEnd_2593105 := by exact prefixLift 2593105
  have htrace : WordTrace (prefixWord ++ tailWord_2593105) baseStart_2593105 baseEnd_2593105 := by
    simpa [prefixWord, tailWord_2593105, baseEnd_2593105] using wordTrace_append hprefix tailTrace_2593105
  have hstable : (prefixWord ++ tailWord_2593105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593105).length < 2 ^ (prefixWord ++ tailWord_2593105).sum := by decide
  have hdescent : baseEnd_2593105 < baseStart_2593105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593122 : List Nat := [3, 3, 2, 1, 1, 2, 2, 1, 2, 2, 4]
def baseStart_2593122 : Nat := 118140960795 + 2593122 * 2 ^ 59
def prefixEnd_2593122 : Nat := 4983230072969 + 3 ^ 40 * 2593122 * 2
def baseEnd_2593122 : Nat := 1331517981748308631949455

theorem tailTrace_2593122 : CollatzResearch.WordTrace tailWord_2593122 prefixEnd_2593122 1331517981748308631949455 := by
  unfold tailWord_2593122
  simp only [CollatzResearch.WordTrace]
  refine ⟨23644732327892334706007405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63052619541046225882686413 23644732327892334706007405)
  ·
    refine ⟨8866774622959625514752777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23644732327892334706007405 8866774622959625514752777)
    ·
      refine ⟨6650080967219719136064583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8866774622959625514752777 6650080967219719136064583)
      ·
        refine ⟨9975121450829578704096875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6650080967219719136064583 9975121450829578704096875)
        ·
          refine ⟨14962682176244368056145313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9975121450829578704096875 14962682176244368056145313)
          ·
            refine ⟨11222011632183276042108985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14962682176244368056145313 11222011632183276042108985)
            ·
              refine ⟨8416508724137457031581739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11222011632183276042108985 8416508724137457031581739)
              ·
                refine ⟨12624763086206185547372609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8416508724137457031581739 12624763086206185547372609)
                ·
                  refine ⟨9468572314654639160529457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12624763086206185547372609 9468572314654639160529457)
                  ·
                    refine ⟨7101429235990979370397093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9468572314654639160529457 7101429235990979370397093)
                    ·
                      refine ⟨1331517981748308631949455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7101429235990979370397093 1331517981748308631949455)
                      ·
                        rfl

theorem cell23_2593122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_2593122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2593122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2593122 prefixEnd_2593122 := by exact prefixLift 2593122
  have htrace : WordTrace (prefixWord ++ tailWord_2593122) baseStart_2593122 baseEnd_2593122 := by
    simpa [prefixWord, tailWord_2593122, baseEnd_2593122] using wordTrace_append hprefix tailTrace_2593122
  have hstable : (prefixWord ++ tailWord_2593122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593122).length < 2 ^ (prefixWord ++ tailWord_2593122).sum := by decide
  have hdescent : baseEnd_2593122 < baseStart_2593122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593145 : List Nat := [1, 2, 1, 3, 2, 1, 1, 5, 2, 5]
def baseStart_2593145 : Nat := 118140960795 + 2593145 * 2 ^ 59
def prefixEnd_2593145 : Nat := 4983230072969 + 3 ^ 40 * 2593145 * 2
def baseEnd_2593145 : Nat := 443843263934454013987283

theorem tailTrace_2593145 : CollatzResearch.WordTrace tailWord_2593145 prefixEnd_2593145 443843263934454013987283 := by
  unfold tailWord_2593145
  simp only [CollatzResearch.WordTrace]
  refine ⟨94579768190486013752116889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63053178793657342501411259 94579768190486013752116889)
  ·
    refine ⟨70934826142864510314087667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94579768190486013752116889 70934826142864510314087667)
    ·
      refine ⟨106402239214296765471131501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70934826142864510314087667 106402239214296765471131501)
      ·
        refine ⟨39900839705361287051674313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106402239214296765471131501 39900839705361287051674313)
        ·
          refine ⟨29925629779020965288755735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39900839705361287051674313 29925629779020965288755735)
          ·
            refine ⟨44888444668531447933133603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29925629779020965288755735 44888444668531447933133603)
            ·
              refine ⟨67332667002797171899700405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44888444668531447933133603 67332667002797171899700405)
              ·
                refine ⟨6312437531512234865596913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67332667002797171899700405 6312437531512234865596913)
                ·
                  refine ⟨4734328148634176149197685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6312437531512234865596913 4734328148634176149197685)
                  ·
                    refine ⟨443843263934454013987283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4734328148634176149197685 443843263934454013987283)
                    ·
                      rfl

theorem cell23_2593145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5, 2, 5].length) (baseStart_2593145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2593145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2593145 prefixEnd_2593145 := by exact prefixLift 2593145
  have htrace : WordTrace (prefixWord ++ tailWord_2593145) baseStart_2593145 baseEnd_2593145 := by
    simpa [prefixWord, tailWord_2593145, baseEnd_2593145] using wordTrace_append hprefix tailTrace_2593145
  have hstable : (prefixWord ++ tailWord_2593145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593145).length < 2 ^ (prefixWord ++ tailWord_2593145).sum := by decide
  have hdescent : baseEnd_2593145 < baseStart_2593145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593149 : List Nat := [1, 4, 1, 1, 2, 5, 1, 3, 5]
def baseStart_2593149 : Nat := 118140960795 + 2593149 * 2 ^ 59
def prefixEnd_2593149 : Nat := 4983230072969 + 3 ^ 40 * 2593149 * 2
def baseEnd_2593149 : Nat := 147947982858442225145759

theorem tailTrace_2593149 : CollatzResearch.WordTrace tailWord_2593149 prefixEnd_2593149 147947982858442225145759 := by
  unfold tailWord_2593149
  simp only [CollatzResearch.WordTrace]
  refine ⟨94579914082471522435262501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63053276054981014956841667 94579914082471522435262501)
  ·
    refine ⟨17733733890463410456611719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94579914082471522435262501 17733733890463410456611719)
    ·
      refine ⟨26600600835695115684917579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17733733890463410456611719 26600600835695115684917579)
      ·
        refine ⟨39900901253542673527376369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26600600835695115684917579 39900901253542673527376369)
        ·
          refine ⟨29925675940157005145532277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39900901253542673527376369 29925675940157005145532277)
          ·
            refine ⟨2805532119389719232393651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29925675940157005145532277 2805532119389719232393651)
            ·
              refine ⟨4208298179084578848590477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2805532119389719232393651 4208298179084578848590477)
              ·
                refine ⟨1578111817156717068221429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4208298179084578848590477 1578111817156717068221429)
                ·
                  refine ⟨147947982858442225145759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1578111817156717068221429 147947982858442225145759)
                  ·
                    rfl

theorem cell23_2593149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 3, 5].length) (baseStart_2593149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2593149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2593149 prefixEnd_2593149 := by exact prefixLift 2593149
  have htrace : WordTrace (prefixWord ++ tailWord_2593149) baseStart_2593149 baseEnd_2593149 := by
    simpa [prefixWord, tailWord_2593149, baseEnd_2593149] using wordTrace_append hprefix tailTrace_2593149
  have hstable : (prefixWord ++ tailWord_2593149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593149).length < 2 ^ (prefixWord ++ tailWord_2593149).sum := by decide
  have hdescent : baseEnd_2593149 < baseStart_2593149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593166 : List Nat := [4, 1, 1, 4, 1, 2, 3, 2, 5]
def baseStart_2593166 : Nat := 118140960795 + 2593166 * 2 ^ 59
def prefixEnd_2593166 : Nat := 4983230072969 + 3 ^ 40 * 2593166 * 2
def baseEnd_2593166 : Nat := 147948952766345162199917

theorem tailTrace_2593166 : CollatzResearch.WordTrace tailWord_2593166 prefixEnd_2593166 147948952766345162199917 := by
  unfold tailWord_2593166
  simp only [CollatzResearch.WordTrace]
  refine ⟨11822566765426241792328919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63053689415606622892420901 11822566765426241792328919)
  ·
    refine ⟨17733850148139362688493379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11822566765426241792328919 17733850148139362688493379)
    ·
      refine ⟨26600775222209044032740069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17733850148139362688493379 26600775222209044032740069)
      ·
        refine ⟨4987645354164195756138763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26600775222209044032740069 4987645354164195756138763)
        ·
          refine ⟨7481468031246293634208145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4987645354164195756138763 7481468031246293634208145)
          ·
            refine ⟨5611101023434720225656109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7481468031246293634208145 5611101023434720225656109)
            ·
              refine ⟨2104162883788020084621041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5611101023434720225656109 2104162883788020084621041)
              ·
                refine ⟨1578122162841015063465781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2104162883788020084621041 1578122162841015063465781)
                ·
                  refine ⟨147948952766345162199917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1578122162841015063465781 147948952766345162199917)
                  ·
                    rfl

theorem cell23_2593166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 2, 5].length) (baseStart_2593166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2593166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2593166 prefixEnd_2593166 := by exact prefixLift 2593166
  have htrace : WordTrace (prefixWord ++ tailWord_2593166) baseStart_2593166 baseEnd_2593166 := by
    simpa [prefixWord, tailWord_2593166, baseEnd_2593166] using wordTrace_append hprefix tailTrace_2593166
  have hstable : (prefixWord ++ tailWord_2593166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593166).length < 2 ^ (prefixWord ++ tailWord_2593166).sum := by decide
  have hdescent : baseEnd_2593166 < baseStart_2593166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593217 : List Nat := [1, 2, 7, 1, 2, 1, 2, 2, 5]
def baseStart_2593217 : Nat := 118140960795 + 2593217 * 2 ^ 59
def prefixEnd_2593217 : Nat := 4983230072969 + 3 ^ 40 * 2593217 * 2
def baseEnd_2593217 : Nat := 147951862490053973362391

theorem tailTrace_2593217 : CollatzResearch.WordTrace tailWord_2593217 prefixEnd_2593217 147951862490053973362391 := by
  unfold tailWord_2593217
  simp only [CollatzResearch.WordTrace]
  refine ⟨94582394246225170048737905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63054929497483446699158603 94582394246225170048737905)
  ·
    refine ⟨70936795684668877536553429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94582394246225170048737905 70936795684668877536553429)
    ·
      refine ⟨1662581148859426817262971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 70936795684668877536553429 1662581148859426817262971)
      ·
        refine ⟨2493871723289140225894457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1662581148859426817262971 2493871723289140225894457)
        ·
          refine ⟨1870403792466855169420843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2493871723289140225894457 1870403792466855169420843)
          ·
            refine ⟨2805605688700282754131265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1870403792466855169420843 2805605688700282754131265)
            ·
              refine ⟨2104204266525212065598449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2805605688700282754131265 2104204266525212065598449)
              ·
                refine ⟨1578153199893909049198837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2104204266525212065598449 1578153199893909049198837)
                ·
                  refine ⟨147951862490053973362391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1578153199893909049198837 147951862490053973362391)
                  ·
                    rfl

theorem cell23_2593217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 2, 5].length) (baseStart_2593217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2593217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2593217 prefixEnd_2593217 := by exact prefixLift 2593217
  have htrace : WordTrace (prefixWord ++ tailWord_2593217) baseStart_2593217 baseEnd_2593217 := by
    simpa [prefixWord, tailWord_2593217, baseEnd_2593217] using wordTrace_append hprefix tailTrace_2593217
  have hstable : (prefixWord ++ tailWord_2593217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593217).length < 2 ^ (prefixWord ++ tailWord_2593217).sum := by decide
  have hdescent : baseEnd_2593217 < baseStart_2593217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593249 : List Nat := [1, 2, 3, 1, 2, 2, 3, 2, 3, 1, 3]
def baseStart_2593249 : Nat := 118140960795 + 2593249 * 2 ^ 59
def prefixEnd_2593249 : Nat := 4983230072969 + 3 ^ 40 * 2593249 * 2
def baseEnd_2593249 : Nat := 1331583193791429635061371

theorem tailTrace_2593249 : CollatzResearch.WordTrace tailWord_2593249 prefixEnd_2593249 1331583193791429635061371 := by
  unfold tailWord_2593249
  simp only [CollatzResearch.WordTrace]
  refine ⟨94583561382109239513902801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63055707588072826342601867 94583561382109239513902801)
  ·
    refine ⟨70937671036581929635427101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94583561382109239513902801 70937671036581929635427101)
    ·
      refine ⟨26601626638718223613285163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70937671036581929635427101 26601626638718223613285163)
      ·
        refine ⟨39902439958077335419927745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26601626638718223613285163 39902439958077335419927745)
        ·
          refine ⟨29926829968558001564945809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39902439958077335419927745 29926829968558001564945809)
          ·
            refine ⟨22445122476418501173709357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29926829968558001564945809 22445122476418501173709357)
            ·
              refine ⟨8416920928656937940141009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22445122476418501173709357 8416920928656937940141009)
              ·
                refine ⟨6312690696492703455105757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8416920928656937940141009 6312690696492703455105757)
                ·
                  refine ⟨2367259011184763795664659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6312690696492703455105757 2367259011184763795664659)
                  ·
                    refine ⟨3550888516777145693496989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2367259011184763795664659 3550888516777145693496989)
                    ·
                      refine ⟨1331583193791429635061371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3550888516777145693496989 1331583193791429635061371)
                      ·
                        rfl

theorem cell23_2593249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2, 3, 1, 3].length) (baseStart_2593249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2593249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2593249 prefixEnd_2593249 := by exact prefixLift 2593249
  have htrace : WordTrace (prefixWord ++ tailWord_2593249) baseStart_2593249 baseEnd_2593249 := by
    simpa [prefixWord, tailWord_2593249, baseEnd_2593249] using wordTrace_append hprefix tailTrace_2593249
  have hstable : (prefixWord ++ tailWord_2593249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593249).length < 2 ^ (prefixWord ++ tailWord_2593249).sum := by decide
  have hdescent : baseEnd_2593249 < baseStart_2593249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593250 : List Nat := [3, 3, 3, 2, 2, 1, 1, 1, 2, 1, 4]
def baseStart_2593250 : Nat := 118140960795 + 2593250 * 2 ^ 59
def prefixEnd_2593250 : Nat := 4983230072969 + 3 ^ 40 * 2593250 * 2
def baseEnd_2593250 : Nat := 1331583707272084131148867

theorem tailTrace_2593250 : CollatzResearch.WordTrace tailWord_2593250 prefixEnd_2593250 1331583707272084131148867 := by
  unfold tailWord_2593250
  simp only [CollatzResearch.WordTrace]
  refine ⟨23645899463776404171172301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63055731903403744456459469 23645899463776404171172301)
  ·
    refine ⟨8867212298916151564189613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23645899463776404171172301 8867212298916151564189613)
    ·
      refine ⟨3325204612093556836571105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8867212298916151564189613 3325204612093556836571105)
      ·
        refine ⟨2493903459070167627428329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3325204612093556836571105 2493903459070167627428329)
        ·
          refine ⟨1870427594302625720571247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2493903459070167627428329 1870427594302625720571247)
          ·
            refine ⟨2805641391453938580856871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1870427594302625720571247 2805641391453938580856871)
            ·
              refine ⟨4208462087180907871285307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2805641391453938580856871 4208462087180907871285307)
              ·
                refine ⟨6312693130771361806927961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4208462087180907871285307 6312693130771361806927961)
                ·
                  refine ⟨4734519848078521355195971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6312693130771361806927961 4734519848078521355195971)
                  ·
                    refine ⟨7101779772117782032793957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4734519848078521355195971 7101779772117782032793957)
                    ·
                      refine ⟨1331583707272084131148867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7101779772117782032793957 1331583707272084131148867)
                      ·
                        rfl

theorem cell23_2593250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_2593250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2593250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2593250 prefixEnd_2593250 := by exact prefixLift 2593250
  have htrace : WordTrace (prefixWord ++ tailWord_2593250) baseStart_2593250 baseEnd_2593250 := by
    simpa [prefixWord, tailWord_2593250, baseEnd_2593250] using wordTrace_append hprefix tailTrace_2593250
  have hstable : (prefixWord ++ tailWord_2593250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593250).length < 2 ^ (prefixWord ++ tailWord_2593250).sum := by decide
  have hdescent : baseEnd_2593250 < baseStart_2593250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593253 : List Nat := [1, 3, 1, 5, 3, 1, 1, 1, 2, 2, 3]
def baseStart_2593253 : Nat := 118140960795 + 2593253 * 2 ^ 59
def prefixEnd_2593253 : Nat := 4983230072969 + 3 ^ 40 * 2593253 * 2
def baseEnd_2593253 : Nat := 1331585247714047619411353

theorem tailTrace_2593253 : CollatzResearch.WordTrace tailWord_2593253 prefixEnd_2593253 1331585247714047619411353 := by
  unfold tailWord_2593253
  simp only [CollatzResearch.WordTrace]
  refine ⟨94583707274094748197048413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63055804849396498798032275 94583707274094748197048413)
  ·
    refine ⟨35468890227785530573893155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94583707274094748197048413 35468890227785530573893155)
    ·
      refine ⟨53203335341678295860839733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35468890227785530573893155 53203335341678295860839733)
      ·
        refine ⟨4987812688282340236953725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53203335341678295860839733 4987812688282340236953725)
        ·
          refine ⟨1870429758105877588857647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4987812688282340236953725 1870429758105877588857647)
          ·
            refine ⟨2805644637158816383286471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1870429758105877588857647 2805644637158816383286471)
            ·
              refine ⟨4208466955738224574929707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2805644637158816383286471 4208466955738224574929707)
              ·
                refine ⟨6312700433607336862394561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4208466955738224574929707 6312700433607336862394561)
                ·
                  refine ⟨4734525325205502646795921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6312700433607336862394561 4734525325205502646795921)
                  ·
                    refine ⟨3550893993904126985096941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4734525325205502646795921 3550893993904126985096941)
                    ·
                      refine ⟨1331585247714047619411353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3550893993904126985096941 1331585247714047619411353)
                      ·
                        rfl

theorem cell23_2593253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_2593253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2593253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2593253 prefixEnd_2593253 := by exact prefixLift 2593253
  have htrace : WordTrace (prefixWord ++ tailWord_2593253) baseStart_2593253 baseEnd_2593253 := by
    simpa [prefixWord, tailWord_2593253, baseEnd_2593253] using wordTrace_append hprefix tailTrace_2593253
  have hstable : (prefixWord ++ tailWord_2593253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593253).length < 2 ^ (prefixWord ++ tailWord_2593253).sum := by decide
  have hdescent : baseEnd_2593253 < baseStart_2593253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593292 : List Nat := [2, 2, 1, 2, 4, 1, 1, 1, 3, 1, 5]
def baseStart_2593292 : Nat := 118140960795 + 2593292 * 2 ^ 59
def prefixEnd_2593292 : Nat := 4983230072969 + 3 ^ 40 * 2593292 * 2
def baseEnd_2593292 : Nat := 1331605273459572966823673

theorem tailTrace_2593292 : CollatzResearch.WordTrace tailWord_2593292 prefixEnd_2593292 1331605273459572966823673 := by
  unfold tailWord_2593292
  simp only [CollatzResearch.WordTrace]
  refine ⟨47292564860476728928859065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63056753147302305238478753 47292564860476728928859065)
  ·
    refine ⟨35469423645357546696644299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47292564860476728928859065 35469423645357546696644299)
    ·
      refine ⟨53204135468036320044966449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35469423645357546696644299 53204135468036320044966449)
      ·
        refine ⟨39903101601027240033724837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53204135468036320044966449 39903101601027240033724837)
        ·
          refine ⟨7481831550192607506323407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39903101601027240033724837 7481831550192607506323407)
          ·
            refine ⟨11222747325288911259485111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7481831550192607506323407 11222747325288911259485111)
            ·
              refine ⟨16834120987933366889227667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11222747325288911259485111 16834120987933366889227667)
              ·
                refine ⟨25251181481900050333841501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16834120987933366889227667 25251181481900050333841501)
                ·
                  refine ⟨9469193055712518875190563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25251181481900050333841501 9469193055712518875190563)
                  ·
                    refine ⟨14203789583568778312785845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9469193055712518875190563 14203789583568778312785845)
                    ·
                      refine ⟨1331605273459572966823673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14203789583568778312785845 1331605273459572966823673)
                      ·
                        rfl

theorem cell23_2593292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_2593292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2593292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2593292 prefixEnd_2593292 := by exact prefixLift 2593292
  have htrace : WordTrace (prefixWord ++ tailWord_2593292) baseStart_2593292 baseEnd_2593292 := by
    simpa [prefixWord, tailWord_2593292, baseEnd_2593292] using wordTrace_append hprefix tailTrace_2593292
  have hstable : (prefixWord ++ tailWord_2593292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593292).length < 2 ^ (prefixWord ++ tailWord_2593292).sum := by decide
  have hdescent : baseEnd_2593292 < baseStart_2593292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593293 : List Nat := [1, 7, 1, 1, 1, 1, 1, 2, 1, 5, 2]
def baseStart_2593293 : Nat := 118140960795 + 2593293 * 2 ^ 59
def prefixEnd_2593293 : Nat := 4983230072969 + 3 ^ 40 * 2593293 * 2
def baseEnd_2593293 : Nat := 1331605786940227462911169

theorem tailTrace_2593293 : CollatzResearch.WordTrace tailWord_2593293 prefixEnd_2593293 1331605786940227462911169 := by
  unfold tailWord_2593293
  simp only [CollatzResearch.WordTrace]
  refine ⟨94585166193949835028504533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63056777462633223352336355 94585166193949835028504533)
  ·
    refine ⟨2216839832670699258480575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 94585166193949835028504533 2216839832670699258480575)
    ·
      refine ⟨3325259749006048887720863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2216839832670699258480575 3325259749006048887720863)
      ·
        refine ⟨4987889623509073331581295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3325259749006048887720863 4987889623509073331581295)
        ·
          refine ⟨7481834435263609997371943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4987889623509073331581295 7481834435263609997371943)
          ·
            refine ⟨11222751652895414996057915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7481834435263609997371943 11222751652895414996057915)
            ·
              refine ⟨16834127479343122494086873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11222751652895414996057915 16834127479343122494086873)
              ·
                refine ⟨12625595609507341870565155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16834127479343122494086873 12625595609507341870565155)
                ·
                  refine ⟨18938393414261012805847733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12625595609507341870565155 18938393414261012805847733)
                  ·
                    refine ⟨1775474382586969950548225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18938393414261012805847733 1775474382586969950548225)
                    ·
                      refine ⟨1331605786940227462911169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1775474382586969950548225 1331605786940227462911169)
                      ·
                        rfl

theorem cell23_2593293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_2593293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2593293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2593293 prefixEnd_2593293 := by exact prefixLift 2593293
  have htrace : WordTrace (prefixWord ++ tailWord_2593293) baseStart_2593293 baseEnd_2593293 := by
    simpa [prefixWord, tailWord_2593293, baseEnd_2593293] using wordTrace_append hprefix tailTrace_2593293
  have hstable : (prefixWord ++ tailWord_2593293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593293).length < 2 ^ (prefixWord ++ tailWord_2593293).sum := by decide
  have hdescent : baseEnd_2593293 < baseStart_2593293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593305 : List Nat := [1, 2, 1, 2, 1, 1, 2, 2, 2, 2, 7]
def baseStart_2593305 : Nat := 118140960795 + 2593305 * 2 ^ 59
def prefixEnd_2593305 : Nat := 4983230072969 + 3 ^ 40 * 2593305 * 2
def baseEnd_2593305 : Nat := 1331611948708081415961113

theorem tailTrace_2593305 : CollatzResearch.WordTrace tailWord_2593305 prefixEnd_2593305 1331611948708081415961113 := by
  unfold tailWord_2593305
  simp only [CollatzResearch.WordTrace]
  refine ⟨94585603869906361077941369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63057069246604240718627579 94585603869906361077941369)
  ·
    refine ⟨70939202902429770808456027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94585603869906361077941369 70939202902429770808456027)
    ·
      refine ⟨106408804353644656212684041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70939202902429770808456027 106408804353644656212684041)
      ·
        refine ⟨79806603265233492159513031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106408804353644656212684041 79806603265233492159513031)
        ·
          refine ⟨119709904897850238239269547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79806603265233492159513031 119709904897850238239269547)
          ·
            refine ⟨179564857346775357358904321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119709904897850238239269547 179564857346775357358904321)
            ·
              refine ⟨134673643010081518019178241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179564857346775357358904321 134673643010081518019178241)
              ·
                refine ⟨101005232257561138514383681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134673643010081518019178241 101005232257561138514383681)
                ·
                  refine ⟨75753924193170853885787761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101005232257561138514383681 75753924193170853885787761)
                  ·
                    refine ⟨56815443144878140414340821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 75753924193170853885787761 56815443144878140414340821)
                    ·
                      refine ⟨1331611948708081415961113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 56815443144878140414340821 1331611948708081415961113)
                      ·
                        rfl

theorem cell23_2593305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 2, 7].length) (baseStart_2593305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2593305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2593305 prefixEnd_2593305 := by exact prefixLift 2593305
  have htrace : WordTrace (prefixWord ++ tailWord_2593305) baseStart_2593305 baseEnd_2593305 := by
    simpa [prefixWord, tailWord_2593305, baseEnd_2593305] using wordTrace_append hprefix tailTrace_2593305
  have hstable : (prefixWord ++ tailWord_2593305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593305).length < 2 ^ (prefixWord ++ tailWord_2593305).sum := by decide
  have hdescent : baseEnd_2593305 < baseStart_2593305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593306 : List Nat := [3, 1, 1, 3, 1, 1, 4, 2, 3, 2, 2]
def baseStart_2593306 : Nat := 118140960795 + 2593306 * 2 ^ 59
def prefixEnd_2593306 : Nat := 4983230072969 + 3 ^ 40 * 2593306 * 2
def baseEnd_2593306 : Nat := 1331612462188735912048609

theorem tailTrace_2593306 : CollatzResearch.WordTrace tailWord_2593306 prefixEnd_2593306 1331612462188735912048609 := by
  unfold tailWord_2593306
  simp only [CollatzResearch.WordTrace]
  refine ⟨23646410085725684562181943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63057093561935158832485181 23646410085725684562181943)
  ·
    refine ⟨35469615128588526843272915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23646410085725684562181943 35469615128588526843272915)
    ·
      refine ⟨53204422692882790264909373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35469615128588526843272915 53204422692882790264909373)
      ·
        refine ⟨19951658509831046349341015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53204422692882790264909373 19951658509831046349341015)
        ·
          refine ⟨29927487764746569524011523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19951658509831046349341015 29927487764746569524011523)
          ·
            refine ⟨44891231647119854286017285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29927487764746569524011523 44891231647119854286017285)
            ·
              refine ⟨8417105933834972678628241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44891231647119854286017285 8417105933834972678628241)
              ·
                refine ⟨6312829450376229508971181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8417105933834972678628241 6312829450376229508971181)
                ·
                  refine ⟨2367311043891086065864193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6312829450376229508971181 2367311043891086065864193)
                  ·
                    refine ⟨1775483282918314549398145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2367311043891086065864193 1775483282918314549398145)
                    ·
                      refine ⟨1331612462188735912048609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1775483282918314549398145 1331612462188735912048609)
                      ·
                        rfl

theorem cell23_2593306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2, 3, 2, 2].length) (baseStart_2593306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2593306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2593306 prefixEnd_2593306 := by exact prefixLift 2593306
  have htrace : WordTrace (prefixWord ++ tailWord_2593306) baseStart_2593306 baseEnd_2593306 := by
    simpa [prefixWord, tailWord_2593306, baseEnd_2593306] using wordTrace_append hprefix tailTrace_2593306
  have hstable : (prefixWord ++ tailWord_2593306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593306).length < 2 ^ (prefixWord ++ tailWord_2593306).sum := by decide
  have hdescent : baseEnd_2593306 < baseStart_2593306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593326 : List Nat := [4, 1, 3, 1, 3, 1, 2, 1, 1, 1, 5]
def baseStart_2593326 : Nat := 118140960795 + 2593326 * 2 ^ 59
def prefixEnd_2593326 : Nat := 4983230072969 + 3 ^ 40 * 2593326 * 2
def baseEnd_2593326 : Nat := 1331622731801825833798517

theorem tailTrace_2593326 : CollatzResearch.WordTrace tailWord_2593326 prefixEnd_2593326 1331622731801825833798517 := by
  unfold tailWord_2593326
  simp only [CollatzResearch.WordTrace]
  refine ⟨11823296225353785208056979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63057579868553521109637221 11823296225353785208056979)
  ·
    refine ⟨17734944338030677812085469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11823296225353785208056979 17734944338030677812085469)
    ·
      refine ⟨6650604126761504179532051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17734944338030677812085469 6650604126761504179532051)
      ·
        refine ⟨9975906190142256269298077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6650604126761504179532051 9975906190142256269298077)
        ·
          refine ⟨3740964821303346100986779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9975906190142256269298077 3740964821303346100986779)
          ·
            refine ⟨5611447231955019151480169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3740964821303346100986779 5611447231955019151480169)
            ·
              refine ⟨4208585423966264363610127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5611447231955019151480169 4208585423966264363610127)
              ·
                refine ⟨6312878135949396545415191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4208585423966264363610127 6312878135949396545415191)
                ·
                  refine ⟨9469317203924094818122787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6312878135949396545415191 9469317203924094818122787)
                  ·
                    refine ⟨14203975805886142227184181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9469317203924094818122787 14203975805886142227184181)
                    ·
                      refine ⟨1331622731801825833798517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14203975805886142227184181 1331622731801825833798517)
                      ·
                        rfl

theorem cell23_2593326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_2593326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2593326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2593326 prefixEnd_2593326 := by exact prefixLift 2593326
  have htrace : WordTrace (prefixWord ++ tailWord_2593326) baseStart_2593326 baseEnd_2593326 := by
    simpa [prefixWord, tailWord_2593326, baseEnd_2593326] using wordTrace_append hprefix tailTrace_2593326
  have hstable : (prefixWord ++ tailWord_2593326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593326).length < 2 ^ (prefixWord ++ tailWord_2593326).sum := by decide
  have hdescent : baseEnd_2593326 < baseStart_2593326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593350 : List Nat := [6, 1, 1, 1, 2, 1, 4, 1, 2, 4]
def baseStart_2593350 : Nat := 118140960795 + 2593350 * 2 ^ 59
def prefixEnd_2593350 : Nat := 4983230072969 + 3 ^ 40 * 2593350 * 2
def baseEnd_2593350 : Nat := 443878351779177913299469

theorem tailTrace_2593350 : CollatzResearch.WordTrace tailWord_2593350 prefixEnd_2593350 443878351779177913299469 := by
  unfold tailWord_2593350
  simp only [CollatzResearch.WordTrace]
  refine ⟨2955851411085729180104047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 63058163436495555842219669 2955851411085729180104047)
  ·
    refine ⟨4433777116628593770156071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2955851411085729180104047 4433777116628593770156071)
    ·
      refine ⟨6650665674942890655234107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4433777116628593770156071 6650665674942890655234107)
      ·
        refine ⟨9975998512414335982851161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6650665674942890655234107 9975998512414335982851161)
        ·
          refine ⟨7481998884310751987138371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9975998512414335982851161 7481998884310751987138371)
          ·
            refine ⟨11222998326466127980707557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7481998884310751987138371 11222998326466127980707557)
            ·
              refine ⟨2104312186212398996382667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11222998326466127980707557 2104312186212398996382667)
              ·
                refine ⟨3156468279318598494574001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2104312186212398996382667 3156468279318598494574001)
                ·
                  refine ⟨2367351209488948870930501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3156468279318598494574001 2367351209488948870930501)
                  ·
                    refine ⟨443878351779177913299469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2367351209488948870930501 443878351779177913299469)
                    ·
                      rfl

theorem cell23_2593350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_2593350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2593350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2593350 prefixEnd_2593350 := by exact prefixLift 2593350
  have htrace : WordTrace (prefixWord ++ tailWord_2593350) baseStart_2593350 baseEnd_2593350 := by
    simpa [prefixWord, tailWord_2593350, baseEnd_2593350] using wordTrace_append hprefix tailTrace_2593350
  have hstable : (prefixWord ++ tailWord_2593350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593350).length < 2 ^ (prefixWord ++ tailWord_2593350).sum := by decide
  have hdescent : baseEnd_2593350 < baseStart_2593350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593356 : List Nat := [2, 2, 1, 3, 1, 2, 3, 3, 2, 1, 3]
def baseStart_2593356 : Nat := 118140960795 + 2593356 * 2 ^ 59
def prefixEnd_2593356 : Nat := 4983230072969 + 3 ^ 40 * 2593356 * 2
def baseEnd_2593356 : Nat := 1331638136221460716423379

theorem tailTrace_2593356 : CollatzResearch.WordTrace tailWord_2593356 prefixEnd_2593356 1331638136221460716423379 := by
  unfold tailWord_2593356
  simp only [CollatzResearch.WordTrace]
  refine ⟨47293731996360798394023961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63058309328481064525365281 47293731996360798394023961)
  ·
    refine ⟨35470298997270598795517971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47293731996360798394023961 35470298997270598795517971)
    ·
      refine ⟨53205448495905898193276957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35470298997270598795517971 53205448495905898193276957)
      ·
        refine ⟨19952043185964711822478859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53205448495905898193276957 19952043185964711822478859)
        ·
          refine ⟨29928064778947067733718289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19952043185964711822478859 29928064778947067733718289)
          ·
            refine ⟨22446048584210300800288717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29928064778947067733718289 22446048584210300800288717)
            ·
              refine ⟨8417268219078862800108269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22446048584210300800288717 8417268219078862800108269)
              ·
                refine ⟨3156475582154573550040601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8417268219078862800108269 3156475582154573550040601)
                ·
                  refine ⟨2367356686615930162530451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3156475582154573550040601 2367356686615930162530451)
                  ·
                    refine ⟨3551035029923895243795677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2367356686615930162530451 3551035029923895243795677)
                    ·
                      refine ⟨1331638136221460716423379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3551035029923895243795677 1331638136221460716423379)
                      ·
                        rfl

theorem cell23_2593356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 3, 2, 1, 3].length) (baseStart_2593356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2593356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2593356 prefixEnd_2593356 := by exact prefixLift 2593356
  have htrace : WordTrace (prefixWord ++ tailWord_2593356) baseStart_2593356 baseEnd_2593356 := by
    simpa [prefixWord, tailWord_2593356, baseEnd_2593356] using wordTrace_append hprefix tailTrace_2593356
  have hstable : (prefixWord ++ tailWord_2593356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593356).length < 2 ^ (prefixWord ++ tailWord_2593356).sum := by decide
  have hdescent : baseEnd_2593356 < baseStart_2593356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593409 : List Nat := [1, 2, 4, 2, 1, 1, 3, 1, 2, 2, 4]
def baseStart_2593409 : Nat := 118140960795 + 2593409 * 2 ^ 59
def prefixEnd_2593409 : Nat := 4983230072969 + 3 ^ 40 * 2593409 * 2
def baseEnd_2593409 : Nat := 1331665350696149009060635

theorem tailTrace_2593409 : CollatzResearch.WordTrace tailWord_2593409 prefixEnd_2593409 1331665350696149009060635 := by
  unfold tailWord_2593409
  simp only [CollatzResearch.WordTrace]
  refine ⟨94589397061529586839727281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63059598041019724559818187 94589397061529586839727281)
  ·
    refine ⟨70942047796147190129795461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94589397061529586839727281 70942047796147190129795461)
    ·
      refine ⟨13301633961777598149336649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70942047796147190129795461 13301633961777598149336649)
      ·
        refine ⟨9976225471333198612002487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13301633961777598149336649 9976225471333198612002487)
        ·
          refine ⟨14964338206999797918003731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9976225471333198612002487 14964338206999797918003731)
          ·
            refine ⟨22446507310499696877005597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14964338206999797918003731 22446507310499696877005597)
            ·
              refine ⟨8417440241437386328877099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22446507310499696877005597 8417440241437386328877099)
              ·
                refine ⟨12626160362156079493315649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8417440241437386328877099 12626160362156079493315649)
                ·
                  refine ⟨9469620271617059619986737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12626160362156079493315649 9469620271617059619986737)
                  ·
                    refine ⟨7102215203712794714990053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9469620271617059619986737 7102215203712794714990053)
                    ·
                      refine ⟨1331665350696149009060635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7102215203712794714990053 1331665350696149009060635)
                      ·
                        rfl

theorem cell23_2593409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_2593409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2593409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2593409 prefixEnd_2593409 := by exact prefixLift 2593409
  have htrace : WordTrace (prefixWord ++ tailWord_2593409) baseStart_2593409 baseEnd_2593409 := by
    simpa [prefixWord, tailWord_2593409, baseEnd_2593409] using wordTrace_append hprefix tailTrace_2593409
  have hstable : (prefixWord ++ tailWord_2593409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593409).length < 2 ^ (prefixWord ++ tailWord_2593409).sum := by decide
  have hdescent : baseEnd_2593409 < baseStart_2593409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593413 : List Nat := [1, 3, 1, 1, 4, 2, 2, 3, 2, 2, 2]
def baseStart_2593413 : Nat := 118140960795 + 2593413 * 2 ^ 59
def prefixEnd_2593413 : Nat := 4983230072969 + 3 ^ 40 * 2593413 * 2
def baseEnd_2593413 : Nat := 1331667404618766993410617

theorem tailTrace_2593413 : CollatzResearch.WordTrace tailWord_2593413 prefixEnd_2593413 1331667404618766993410617 := by
  unfold tailWord_2593413
  simp only [CollatzResearch.WordTrace]
  refine ⟨94589542953515095522872893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63059695302343397015248595 94589542953515095522872893)
  ·
    refine ⟨35471078607568160821077335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94589542953515095522872893 35471078607568160821077335)
    ·
      refine ⟨53206617911352241231616003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35471078607568160821077335 53206617911352241231616003)
      ·
        refine ⟨79809926867028361847424005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53206617911352241231616003 79809926867028361847424005)
        ·
          refine ⟨14964361287567817846392001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79809926867028361847424005 14964361287567817846392001)
          ·
            refine ⟨11223270965675863384794001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14964361287567817846392001 11223270965675863384794001)
            ·
              refine ⟨8417453224256897538595501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11223270965675863384794001 8417453224256897538595501)
              ·
                refine ⟨3156544959096336576973313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8417453224256897538595501 3156544959096336576973313)
                ·
                  refine ⟨2367408719322252432729985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3156544959096336576973313 2367408719322252432729985)
                  ·
                    refine ⟨1775556539491689324547489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2367408719322252432729985 1775556539491689324547489)
                    ·
                      refine ⟨1331667404618766993410617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1775556539491689324547489 1331667404618766993410617)
                      ·
                        rfl

theorem cell23_2593413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 3, 2, 2, 2].length) (baseStart_2593413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2593413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2593413 prefixEnd_2593413 := by exact prefixLift 2593413
  have htrace : WordTrace (prefixWord ++ tailWord_2593413) baseStart_2593413 baseEnd_2593413 := by
    simpa [prefixWord, tailWord_2593413, baseEnd_2593413] using wordTrace_append hprefix tailTrace_2593413
  have hstable : (prefixWord ++ tailWord_2593413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593413).length < 2 ^ (prefixWord ++ tailWord_2593413).sum := by decide
  have hdescent : baseEnd_2593413 < baseStart_2593413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593434 : List Nat := [3, 1, 1, 6, 2, 1, 2, 1, 1, 3, 2]
def baseStart_2593434 : Nat := 118140960795 + 2593434 * 2 ^ 59
def prefixEnd_2593434 : Nat := 4983230072969 + 3 ^ 40 * 2593434 * 2
def baseEnd_2593434 : Nat := 1331678187712511411248021

theorem tailTrace_2593434 : CollatzResearch.WordTrace tailWord_2593434 prefixEnd_2593434 1331678187712511411248021 := by
  unfold tailWord_2593434
  simp only [CollatzResearch.WordTrace]
  refine ⟨23647577221609754027346839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63060205924292677406258237 23647577221609754027346839)
  ·
    refine ⟨35471365832414631041020259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23647577221609754027346839 35471365832414631041020259)
    ·
      refine ⟨53207048748621946561530389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35471365832414631041020259 53207048748621946561530389)
      ·
        refine ⟨2494080410091653745071737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 53207048748621946561530389 2494080410091653745071737)
        ·
          refine ⟨1870560307568740308803803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2494080410091653745071737 1870560307568740308803803)
          ·
            refine ⟨2805840461353110463205705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1870560307568740308803803 2805840461353110463205705)
            ·
              refine ⟨2104380346014832847404279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2805840461353110463205705 2104380346014832847404279)
              ·
                refine ⟨3156570519022249271106419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2104380346014832847404279 3156570519022249271106419)
                ·
                  refine ⟨4734855778533373906659629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3156570519022249271106419 4734855778533373906659629)
                  ·
                    refine ⟨1775570916950015214997361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4734855778533373906659629 1775570916950015214997361)
                    ·
                      refine ⟨1331678187712511411248021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1775570916950015214997361 1331678187712511411248021)
                      ·
                        rfl

theorem cell23_2593434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_2593434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2593434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2593434 prefixEnd_2593434 := by exact prefixLift 2593434
  have htrace : WordTrace (prefixWord ++ tailWord_2593434) baseStart_2593434 baseEnd_2593434 := by
    simpa [prefixWord, tailWord_2593434, baseEnd_2593434] using wordTrace_append hprefix tailTrace_2593434
  have hstable : (prefixWord ++ tailWord_2593434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593434).length < 2 ^ (prefixWord ++ tailWord_2593434).sum := by decide
  have hdescent : baseEnd_2593434 < baseStart_2593434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593436 : List Nat := [2, 2, 3, 2, 2, 1, 1, 5, 5]
def baseStart_2593436 : Nat := 118140960795 + 2593436 * 2 ^ 59
def prefixEnd_2593436 : Nat := 4983230072969 + 3 ^ 40 * 2593436 * 2
def baseEnd_2593436 : Nat := 147964357185980044824779

theorem tailTrace_2593436 : CollatzResearch.WordTrace tailWord_2593436 prefixEnd_2593436 147964357185980044824779 := by
  unfold tailWord_2593436
  simp only [CollatzResearch.WordTrace]
  refine ⟨47295190916215885225480081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63060254554954513633973441 47295190916215885225480081)
  ·
    refine ⟨35471393187161913919110061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47295190916215885225480081 35471393187161913919110061)
    ·
      refine ⟨13301772445185717719666273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35471393187161913919110061 13301772445185717719666273)
      ·
        refine ⟨9976329333889288289749705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13301772445185717719666273 9976329333889288289749705)
        ·
          refine ⟨7482247000416966217312279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9976329333889288289749705 7482247000416966217312279)
          ·
            refine ⟨11223370500625449325968419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7482247000416966217312279 11223370500625449325968419)
            ·
              refine ⟨16835055750938173988952629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11223370500625449325968419 16835055750938173988952629)
              ·
                refine ⟨1578286476650453811464309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16835055750938173988952629 1578286476650453811464309)
                ·
                  refine ⟨147964357185980044824779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1578286476650453811464309 147964357185980044824779)
                  ·
                    rfl

theorem cell23_2593436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 5, 5].length) (baseStart_2593436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2593436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2593436 prefixEnd_2593436 := by exact prefixLift 2593436
  have htrace : WordTrace (prefixWord ++ tailWord_2593436) baseStart_2593436 baseEnd_2593436 := by
    simpa [prefixWord, tailWord_2593436, baseEnd_2593436] using wordTrace_append hprefix tailTrace_2593436
  have hstable : (prefixWord ++ tailWord_2593436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593436).length < 2 ^ (prefixWord ++ tailWord_2593436).sum := by decide
  have hdescent : baseEnd_2593436 < baseStart_2593436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593469 : List Nat := [1, 4, 1, 2, 1, 3, 1, 2, 1, 3, 4]
def baseStart_2593469 : Nat := 118140960795 + 2593469 * 2 ^ 59
def prefixEnd_2593469 : Nat := 4983230072969 + 3 ^ 40 * 2593469 * 2
def baseEnd_2593469 : Nat := 1331696159535418774310359

theorem tailTrace_2593469 : CollatzResearch.WordTrace tailWord_2593469 prefixEnd_2593469 1331696159535418774310359 := by
  unfold tailWord_2593469
  simp only [CollatzResearch.WordTrace]
  refine ⟨94591585441312217086911461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63061056960874811391274307 94591585441312217086911461)
  ·
    refine ⟨17735922270246040703795899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94591585441312217086911461 17735922270246040703795899)
    ·
      refine ⟨26603883405369061055693849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17735922270246040703795899 26603883405369061055693849)
      ·
        refine ⟨19952912554026795791770387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26603883405369061055693849 19952912554026795791770387)
        ·
          refine ⟨29929368831040193687655581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19952912554026795791770387 29929368831040193687655581)
          ·
            refine ⟨11223513311640072632870843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29929368831040193687655581 11223513311640072632870843)
            ·
              refine ⟨16835269967460108949306265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11223513311640072632870843 16835269967460108949306265)
              ·
                refine ⟨12626452475595081711979699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16835269967460108949306265 12626452475595081711979699)
                ·
                  refine ⟨18939678713392622567969549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12626452475595081711979699 18939678713392622567969549)
                  ·
                    refine ⟨7102379517522233462988581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18939678713392622567969549 7102379517522233462988581)
                    ·
                      refine ⟨1331696159535418774310359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7102379517522233462988581 1331696159535418774310359)
                      ·
                        rfl

theorem cell23_2593469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_2593469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2593469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2593469 prefixEnd_2593469 := by exact prefixLift 2593469
  have htrace : WordTrace (prefixWord ++ tailWord_2593469) baseStart_2593469 baseEnd_2593469 := by
    simpa [prefixWord, tailWord_2593469, baseEnd_2593469] using wordTrace_append hprefix tailTrace_2593469
  have hstable : (prefixWord ++ tailWord_2593469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593469).length < 2 ^ (prefixWord ++ tailWord_2593469).sum := by decide
  have hdescent : baseEnd_2593469 < baseStart_2593469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593479 : List Nat := [1, 1, 4, 1, 1, 1, 2, 3, 5, 4]
def baseStart_2593479 : Nat := 118140960795 + 2593479 * 2 ^ 59
def prefixEnd_2593479 : Nat := 4983230072969 + 3 ^ 40 * 2593479 * 2
def baseEnd_2593479 : Nat := 443900431447321245061771

theorem tailTrace_2593479 : CollatzResearch.WordTrace tailWord_2593479 prefixEnd_2593479 443900431447321245061771 := by
  unfold tailWord_2593479
  simp only [CollatzResearch.WordTrace]
  refine ⟨94591950171275988794775491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63061300114183992529850327 94591950171275988794775491)
  ·
    refine ⟨141887925256913983192163237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94591950171275988794775491 141887925256913983192163237)
    ·
      refine ⟨26603985985671371848530607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141887925256913983192163237 26603985985671371848530607)
      ·
        refine ⟨39905978978507057772795911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26603985985671371848530607 39905978978507057772795911)
        ·
          refine ⟨59858968467760586659193867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39905978978507057772795911 59858968467760586659193867)
          ·
            refine ⟨89788452701640879988790801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59858968467760586659193867 89788452701640879988790801)
            ·
              refine ⟨67341339526230659991593101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89788452701640879988790801 67341339526230659991593101)
              ·
                refine ⟨25253002322336497496847413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67341339526230659991593101 25253002322336497496847413)
                ·
                  refine ⟨2367468967719046640329445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25253002322336497496847413 2367468967719046640329445)
                  ·
                    refine ⟨443900431447321245061771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2367468967719046640329445 443900431447321245061771)
                    ·
                      rfl

theorem cell23_2593479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 5, 4].length) (baseStart_2593479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2593479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2593479 prefixEnd_2593479 := by exact prefixLift 2593479
  have htrace : WordTrace (prefixWord ++ tailWord_2593479) baseStart_2593479 baseEnd_2593479 := by
    simpa [prefixWord, tailWord_2593479, baseEnd_2593479] using wordTrace_append hprefix tailTrace_2593479
  have hstable : (prefixWord ++ tailWord_2593479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593479).length < 2 ^ (prefixWord ++ tailWord_2593479).sum := by decide
  have hdescent : baseEnd_2593479 < baseStart_2593479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593489 : List Nat := [1, 2, 2, 1, 2, 3, 1, 3, 1, 4, 3]
def baseStart_2593489 : Nat := 118140960795 + 2593489 * 2 ^ 59
def prefixEnd_2593489 : Nat := 4983230072969 + 3 ^ 40 * 2593489 * 2
def baseEnd_2593489 : Nat := 1331706429148508696060267

theorem tailTrace_2593489 : CollatzResearch.WordTrace tailWord_2593489 prefixEnd_2593489 1331706429148508696060267 := by
  unfold tailWord_2593489
  simp only [CollatzResearch.WordTrace]
  refine ⟨94592314901239760502639521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63061543267493173668426347 94592314901239760502639521)
  ·
    refine ⟨70944236175929820376979641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94592314901239760502639521 70944236175929820376979641)
    ·
      refine ⟨53208177131947365282734731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70944236175929820376979641 53208177131947365282734731)
      ·
        refine ⟨79812265697921047924102097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53208177131947365282734731 79812265697921047924102097)
        ·
          refine ⟨59859199273440785943076573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79812265697921047924102097 59859199273440785943076573)
          ·
            refine ⟨22447199727540294728653715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59859199273440785943076573 22447199727540294728653715)
            ·
              refine ⟨33670799591310442092980573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22447199727540294728653715 33670799591310442092980573)
              ·
                refine ⟨12626549846741415784867715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33670799591310442092980573 12626549846741415784867715)
                ·
                  refine ⟨18939824770112123677301573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12626549846741415784867715 18939824770112123677301573)
                  ·
                    refine ⟨3551217144396023189494045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18939824770112123677301573 3551217144396023189494045)
                    ·
                      refine ⟨1331706429148508696060267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3551217144396023189494045 1331706429148508696060267)
                      ·
                        rfl

theorem cell23_2593489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 4, 3].length) (baseStart_2593489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2593489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2593489 prefixEnd_2593489 := by exact prefixLift 2593489
  have htrace : WordTrace (prefixWord ++ tailWord_2593489) baseStart_2593489 baseEnd_2593489 := by
    simpa [prefixWord, tailWord_2593489, baseEnd_2593489] using wordTrace_append hprefix tailTrace_2593489
  have hstable : (prefixWord ++ tailWord_2593489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593489).length < 2 ^ (prefixWord ++ tailWord_2593489).sum := by decide
  have hdescent : baseEnd_2593489 < baseStart_2593489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593509 : List Nat := [1, 3, 1, 4, 1, 2, 2, 1, 8]
def baseStart_2593509 : Nat := 118140960795 + 2593509 * 2 ^ 59
def prefixEnd_2593509 : Nat := 4983230072969 + 3 ^ 40 * 2593509 * 2
def baseEnd_2593509 : Nat := 147968522084622068645575

theorem tailTrace_2593509 : CollatzResearch.WordTrace tailWord_2593509 prefixEnd_2593509 147968522084622068645575 := by
  unfold tailWord_2593509
  simp only [CollatzResearch.WordTrace]
  refine ⟨94593044361167303918367581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63062029574111535945578387 94593044361167303918367581)
  ·
    refine ⟨35472391635437738969387843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94593044361167303918367581 35472391635437738969387843)
    ·
      refine ⟨53208587453156608454081765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35472391635437738969387843 53208587453156608454081765)
      ·
        refine ⟨9976610147466864085140331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53208587453156608454081765 9976610147466864085140331)
        ·
          refine ⟨14964915221200296127710497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9976610147466864085140331 14964915221200296127710497)
          ·
            refine ⟨11223686415900222095782873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14964915221200296127710497 11223686415900222095782873)
            ·
              refine ⟨8417764811925166571837155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11223686415900222095782873 8417764811925166571837155)
              ·
                refine ⟨12626647217887749857755733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8417764811925166571837155 12626647217887749857755733)
                ·
                  refine ⟨147968522084622068645575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12626647217887749857755733 147968522084622068645575)
                  ·
                    rfl

theorem cell23_2593509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 8].length) (baseStart_2593509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2593509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2593509 prefixEnd_2593509 := by exact prefixLift 2593509
  have htrace : WordTrace (prefixWord ++ tailWord_2593509) baseStart_2593509 baseEnd_2593509 := by
    simpa [prefixWord, tailWord_2593509, baseEnd_2593509] using wordTrace_append hprefix tailTrace_2593509
  have hstable : (prefixWord ++ tailWord_2593509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593509).length < 2 ^ (prefixWord ++ tailWord_2593509).sum := by decide
  have hdescent : baseEnd_2593509 < baseStart_2593509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593526 : List Nat := [5, 1, 1, 1, 1, 2, 3, 3, 6]
def baseStart_2593526 : Nat := 118140960795 + 2593526 * 2 ^ 59
def prefixEnd_2593526 : Nat := 4983230072969 + 3 ^ 40 * 2593526 * 2
def baseEnd_2593526 : Nat := 147969491992525005699733

theorem tailTrace_2593526 : CollatzResearch.WordTrace tailWord_2593526 prefixEnd_2593526 147969491992525005699733 := by
  unfold tailWord_2593526
  simp only [CollatzResearch.WordTrace]
  refine ⟨5912104025131607238858527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63062442934737143881157621 5912104025131607238858527)
  ·
    refine ⟨8868156037697410858287791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5912104025131607238858527 8868156037697410858287791)
    ·
      refine ⟨13302234056546116287431687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8868156037697410858287791 13302234056546116287431687)
      ·
        refine ⟨19953351084819174431147531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13302234056546116287431687 19953351084819174431147531)
        ·
          refine ⟨29930026627228761646721297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19953351084819174431147531 29930026627228761646721297)
          ·
            refine ⟨22447519970421571235040973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29930026627228761646721297 22447519970421571235040973)
            ·
              refine ⟨8417819988908089213140365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22447519970421571235040973 8417819988908089213140365)
              ·
                refine ⟨3156682495840533454927637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8417819988908089213140365 3156682495840533454927637)
                ·
                  refine ⟨147969491992525005699733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3156682495840533454927637 147969491992525005699733)
                  ·
                    rfl

theorem cell23_2593526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 3, 6].length) (baseStart_2593526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2593526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2593526 prefixEnd_2593526 := by exact prefixLift 2593526
  have htrace : WordTrace (prefixWord ++ tailWord_2593526) baseStart_2593526 baseEnd_2593526 := by
    simpa [prefixWord, tailWord_2593526, baseEnd_2593526] using wordTrace_append hprefix tailTrace_2593526
  have hstable : (prefixWord ++ tailWord_2593526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593526).length < 2 ^ (prefixWord ++ tailWord_2593526).sum := by decide
  have hdescent : baseEnd_2593526 < baseStart_2593526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593569 : List Nat := [1, 2, 3, 2, 1, 2, 1, 2, 3, 6]
def baseStart_2593569 : Nat := 118140960795 + 2593569 * 2 ^ 59
def prefixEnd_2593569 : Nat := 4983230072969 + 3 ^ 40 * 2593569 * 2
def baseEnd_2593569 : Nat := 443915835866956127686633

theorem tailTrace_2593569 : CollatzResearch.WordTrace tailWord_2593569 prefixEnd_2593569 443915835866956127686633 := by
  unfold tailWord_2593569
  simp only [CollatzResearch.WordTrace]
  refine ⟨94595232740949934165551761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63063488493966622777034507 94595232740949934165551761)
  ·
    refine ⟨70946424555712450624163821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94595232740949934165551761 70946424555712450624163821)
    ·
      refine ⟨26604909208392168984061433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70946424555712450624163821 26604909208392168984061433)
      ·
        refine ⟨19953681906294126738046075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26604909208392168984061433 19953681906294126738046075)
        ·
          refine ⟨29930522859441190107069113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19953681906294126738046075 29930522859441190107069113)
          ·
            refine ⟨22447892144580892580301835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29930522859441190107069113 22447892144580892580301835)
            ·
              refine ⟨33671838216871338870452753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22447892144580892580301835 33671838216871338870452753)
              ·
                refine ⟨25253878662653504152839565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33671838216871338870452753 25253878662653504152839565)
                ·
                  refine ⟨9470204498495064057314837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25253878662653504152839565 9470204498495064057314837)
                  ·
                    refine ⟨443915835866956127686633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9470204498495064057314837 443915835866956127686633)
                    ·
                      rfl

theorem cell23_2593569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 6].length) (baseStart_2593569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2593569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2593569 prefixEnd_2593569 := by exact prefixLift 2593569
  have htrace : WordTrace (prefixWord ++ tailWord_2593569) baseStart_2593569 baseEnd_2593569 := by
    simpa [prefixWord, tailWord_2593569, baseEnd_2593569] using wordTrace_append hprefix tailTrace_2593569
  have hstable : (prefixWord ++ tailWord_2593569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593569).length < 2 ^ (prefixWord ++ tailWord_2593569).sum := by decide
  have hdescent : baseEnd_2593569 < baseStart_2593569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593576 : List Nat := [2, 1, 5, 1, 1, 1, 1, 1, 5, 1, 4]
def baseStart_2593576 : Nat := 118140960795 + 2593576 * 2 ^ 59
def prefixEnd_2593576 : Nat := 4983230072969 + 3 ^ 40 * 2593576 * 2
def baseEnd_2593576 : Nat := 1331751101965449855672367

theorem tailTrace_2593576 : CollatzResearch.WordTrace tailWord_2593576 prefixEnd_2593576 1331751101965449855672367 := by
  unfold tailWord_2593576
  simp only [CollatzResearch.WordTrace]
  refine ⟨47297744025962287180528291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63063658701283049574037721 47297744025962287180528291)
  ·
    refine ⟨70946616038943430770792437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47297744025962287180528291 70946616038943430770792437)
    ·
      refine ⟨6651245253650946634761791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70946616038943430770792437 6651245253650946634761791)
      ·
        refine ⟨9976867880476419952142687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6651245253650946634761791 9976867880476419952142687)
        ·
          refine ⟨14965301820714629928214031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9976867880476419952142687 14965301820714629928214031)
          ·
            refine ⟨22447952731071944892321047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14965301820714629928214031 22447952731071944892321047)
            ·
              refine ⟨33671929096607917338481571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22447952731071944892321047 33671929096607917338481571)
              ·
                refine ⟨50507893644911876007722357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33671929096607917338481571 50507893644911876007722357)
                ·
                  refine ⟨4735115029210488375723971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50507893644911876007722357 4735115029210488375723971)
                  ·
                    refine ⟨7102672543815732563585957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4735115029210488375723971 7102672543815732563585957)
                    ·
                      refine ⟨1331751101965449855672367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7102672543815732563585957 1331751101965449855672367)
                      ·
                        rfl

theorem cell23_2593576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_2593576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2593576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2593576 prefixEnd_2593576 := by exact prefixLift 2593576
  have htrace : WordTrace (prefixWord ++ tailWord_2593576) baseStart_2593576 baseEnd_2593576 := by
    simpa [prefixWord, tailWord_2593576, baseEnd_2593576] using wordTrace_append hprefix tailTrace_2593576
  have hstable : (prefixWord ++ tailWord_2593576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593576).length < 2 ^ (prefixWord ++ tailWord_2593576).sum := by decide
  have hdescent : baseEnd_2593576 < baseStart_2593576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593579 : List Nat := [1, 1, 1, 1, 2, 1, 2, 3, 2, 6, 3]
def baseStart_2593579 : Nat := 118140960795 + 2593579 * 2 ^ 59
def prefixEnd_2593579 : Nat := 4983230072969 + 3 ^ 40 * 2593579 * 2
def baseEnd_2593579 : Nat := 1331752642407413343934853

theorem tailTrace_2593579 : CollatzResearch.WordTrace tailWord_2593579 prefixEnd_2593579 1331752642407413343934853 := by
  unfold tailWord_2593579
  simp only [CollatzResearch.WordTrace]
  refine ⟨94595597470913705873415791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63063731647275803915610527 94595597470913705873415791)
  ·
    refine ⟨141893396206370558810123687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94595597470913705873415791 141893396206370558810123687)
    ·
      refine ⟨212840094309555838215185531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141893396206370558810123687 212840094309555838215185531)
      ·
        refine ⟨319260141464333757322778297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212840094309555838215185531 319260141464333757322778297)
        ·
          refine ⟨239445106098250317992083723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 319260141464333757322778297 239445106098250317992083723)
          ·
            refine ⟨359167659147375476988125585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239445106098250317992083723 359167659147375476988125585)
            ·
              refine ⟨269375744360531607741094189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 359167659147375476988125585 269375744360531607741094189)
              ·
                refine ⟨101015904135199352902910321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 269375744360531607741094189 101015904135199352902910321)
                ·
                  refine ⟨75761928101399514677182741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101015904135199352902910321 75761928101399514677182741)
                  ·
                    refine ⟨3551340379753102250492941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 75761928101399514677182741 3551340379753102250492941)
                    ·
                      refine ⟨1331752642407413343934853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3551340379753102250492941 1331752642407413343934853)
                      ·
                        rfl

theorem cell23_2593579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 6, 3].length) (baseStart_2593579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2593579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2593579 prefixEnd_2593579 := by exact prefixLift 2593579
  have htrace : WordTrace (prefixWord ++ tailWord_2593579) baseStart_2593579 baseEnd_2593579 := by
    simpa [prefixWord, tailWord_2593579, baseEnd_2593579] using wordTrace_append hprefix tailTrace_2593579
  have hstable : (prefixWord ++ tailWord_2593579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593579).length < 2 ^ (prefixWord ++ tailWord_2593579).sum := by decide
  have hdescent : baseEnd_2593579 < baseStart_2593579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593586 : List Nat := [3, 2, 1, 1, 3, 1, 4, 1, 1, 6]
def baseStart_2593586 : Nat := 118140960795 + 2593586 * 2 ^ 59
def prefixEnd_2593586 : Nat := 4983230072969 + 3 ^ 40 * 2593586 * 2
def baseEnd_2593586 : Nat := 443918745590664938849107

theorem tailTrace_2593586 : CollatzResearch.WordTrace tailWord_2593586 prefixEnd_2593586 443918745590664938849107 := by
  unfold tailWord_2593586
  simp only [CollatzResearch.WordTrace]
  refine ⟨23648963195472086517230153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63063901854592230712613741 23648963195472086517230153)
  ·
    refine ⟨17736722396604064887922615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23648963195472086517230153 17736722396604064887922615)
    ·
      refine ⟨26605083594906097331883923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17736722396604064887922615 26605083594906097331883923)
      ·
        refine ⟨39907625392359145997825885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26605083594906097331883923 39907625392359145997825885)
        ·
          refine ⟨14965359522134679749184707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39907625392359145997825885 14965359522134679749184707)
          ·
            refine ⟨22448039283202019623777061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14965359522134679749184707 22448039283202019623777061)
            ·
              refine ⟨4209007365600378679458199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22448039283202019623777061 4209007365600378679458199)
              ·
                refine ⟨6313511048400568019187299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4209007365600378679458199 6313511048400568019187299)
                ·
                  refine ⟨9470266572600852028780949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6313511048400568019187299 9470266572600852028780949)
                  ·
                    refine ⟨443918745590664938849107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9470266572600852028780949 443918745590664938849107)
                    ·
                      rfl

theorem cell23_2593586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 1, 1, 6].length) (baseStart_2593586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2593586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2593586 prefixEnd_2593586 := by exact prefixLift 2593586
  have htrace : WordTrace (prefixWord ++ tailWord_2593586) baseStart_2593586 baseEnd_2593586 := by
    simpa [prefixWord, tailWord_2593586, baseEnd_2593586] using wordTrace_append hprefix tailTrace_2593586
  have hstable : (prefixWord ++ tailWord_2593586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593586).length < 2 ^ (prefixWord ++ tailWord_2593586).sum := by decide
  have hdescent : baseEnd_2593586 < baseStart_2593586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593597 : List Nat := [1, 4, 1, 4, 2, 2, 1, 1, 2, 3, 2]
def baseStart_2593597 : Nat := 118140960795 + 2593597 * 2 ^ 59
def prefixEnd_2593597 : Nat := 4983230072969 + 3 ^ 40 * 2593597 * 2
def baseEnd_2593597 : Nat := 1331761885059194273509771

theorem tailTrace_2593597 : CollatzResearch.WordTrace tailWord_2593597 prefixEnd_2593597 1331761885059194273509771 := by
  unfold tailWord_2593597
  simp only [CollatzResearch.WordTrace]
  refine ⟨94596253984848494947571045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63064169323232329965047363 94596253984848494947571045)
  ·
    refine ⟨17736797622159092802669571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94596253984848494947571045 17736797622159092802669571)
    ·
      refine ⟨26605196433238639204004357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17736797622159092802669571 26605196433238639204004357)
      ·
        refine ⟨4988474331232244850750817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26605196433238639204004357 4988474331232244850750817)
        ·
          refine ⟨3741355748424183638063113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4988474331232244850750817 3741355748424183638063113)
          ·
            refine ⟨2806016811318137728547335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3741355748424183638063113 2806016811318137728547335)
            ·
              refine ⟨4209025216977206592821003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2806016811318137728547335 4209025216977206592821003)
              ·
                refine ⟨6313537825465809889231505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4209025216977206592821003 6313537825465809889231505)
                ·
                  refine ⟨4735153369099357416923629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6313537825465809889231505 4735153369099357416923629)
                  ·
                    refine ⟨1775682513412259031346361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4735153369099357416923629 1775682513412259031346361)
                    ·
                      refine ⟨1331761885059194273509771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1775682513412259031346361 1331761885059194273509771)
                      ·
                        rfl

theorem cell23_2593597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_2593597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2593597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2593597 prefixEnd_2593597 := by exact prefixLift 2593597
  have htrace : WordTrace (prefixWord ++ tailWord_2593597) baseStart_2593597 baseEnd_2593597 := by
    simpa [prefixWord, tailWord_2593597, baseEnd_2593597] using wordTrace_append hprefix tailTrace_2593597
  have hstable : (prefixWord ++ tailWord_2593597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593597).length < 2 ^ (prefixWord ++ tailWord_2593597).sum := by decide
  have hdescent : baseEnd_2593597 < baseStart_2593597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593643 : List Nat := [1, 1, 1, 1, 2, 2, 4, 5, 2, 1, 3]
def baseStart_2593643 : Nat := 118140960795 + 2593643 * 2 ^ 59
def prefixEnd_2593643 : Nat := 4983230072969 + 3 ^ 40 * 2593643 * 2
def baseEnd_2593643 : Nat := 1331785505169301093534559

theorem tailTrace_2593643 : CollatzResearch.WordTrace tailWord_2593643 prefixEnd_2593643 1331785505169301093534559 := by
  unfold tailWord_2593643
  simp only [CollatzResearch.WordTrace]
  refine ⟨94597931742681844803745583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63065287828454563202497055 94597931742681844803745583)
  ·
    refine ⟨141896897614022767205618375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94597931742681844803745583 141896897614022767205618375)
    ·
      refine ⟨212845346421034150808427563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141896897614022767205618375 212845346421034150808427563)
      ·
        refine ⟨319268019631551226212641345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212845346421034150808427563 319268019631551226212641345)
        ·
          refine ⟨239451014723663419659481009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 319268019631551226212641345 239451014723663419659481009)
          ·
            refine ⟨179588261042747564744610757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 239451014723663419659481009 179588261042747564744610757)
            ·
              refine ⟨33672798945515168389614517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 179588261042747564744610757 33672798945515168389614517)
              ·
                refine ⟨3156824901142047036526361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33672798945515168389614517 3156824901142047036526361)
                ·
                  refine ⟨2367618675856535277394771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3156824901142047036526361 2367618675856535277394771)
                  ·
                    refine ⟨3551428013784802916092157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2367618675856535277394771 3551428013784802916092157)
                    ·
                      refine ⟨1331785505169301093534559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3551428013784802916092157 1331785505169301093534559)
                      ·
                        rfl

theorem cell23_2593643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 5, 2, 1, 3].length) (baseStart_2593643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2593643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2593643 prefixEnd_2593643 := by exact prefixLift 2593643
  have htrace : WordTrace (prefixWord ++ tailWord_2593643) baseStart_2593643 baseEnd_2593643 := by
    simpa [prefixWord, tailWord_2593643, baseEnd_2593643] using wordTrace_append hprefix tailTrace_2593643
  have hstable : (prefixWord ++ tailWord_2593643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593643).length < 2 ^ (prefixWord ++ tailWord_2593643).sum := by decide
  have hdescent : baseEnd_2593643 < baseStart_2593643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593659 : List Nat := [1, 1, 1, 1, 1, 5, 2, 2, 1, 8]
def baseStart_2593659 : Nat := 118140960795 + 2593659 * 2 ^ 59
def prefixEnd_2593659 : Nat := 4983230072969 + 3 ^ 40 * 2593659 * 2
def baseEnd_2593659 : Nat := 443931240286591010311495

theorem tailTrace_2593659 : CollatzResearch.WordTrace tailWord_2593659 prefixEnd_2593659 443931240286591010311495 := by
  unfold tailWord_2593659
  simp only [CollatzResearch.WordTrace]
  refine ⟨94598515310623879536328031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63065676873749253024218687 94598515310623879536328031)
  ·
    refine ⟨141897772965935819304492047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94598515310623879536328031 141897772965935819304492047)
    ·
      refine ⟨212846659448903728956738071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141897772965935819304492047 212846659448903728956738071)
      ·
        refine ⟨319269989173355593435107107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212846659448903728956738071 319269989173355593435107107)
        ·
          refine ⟨478904983760033390152660661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319269989173355593435107107 478904983760033390152660661)
          ·
            refine ⟨44897342227503130326811937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 478904983760033390152660661 44897342227503130326811937)
            ·
              refine ⟨33673006670627347745108953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44897342227503130326811937 33673006670627347745108953)
              ·
                refine ⟨25254755002970510808831715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33673006670627347745108953 25254755002970510808831715)
                ·
                  refine ⟨37882132504455766213247573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25254755002970510808831715 37882132504455766213247573)
                  ·
                    refine ⟨443931240286591010311495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 37882132504455766213247573 443931240286591010311495)
                    ·
                      rfl

theorem cell23_2593659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 8].length) (baseStart_2593659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2593659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2593659 prefixEnd_2593659 := by exact prefixLift 2593659
  have htrace : WordTrace (prefixWord ++ tailWord_2593659) baseStart_2593659 baseEnd_2593659 := by
    simpa [prefixWord, tailWord_2593659, baseEnd_2593659] using wordTrace_append hprefix tailTrace_2593659
  have hstable : (prefixWord ++ tailWord_2593659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593659).length < 2 ^ (prefixWord ++ tailWord_2593659).sum := by decide
  have hdescent : baseEnd_2593659 < baseStart_2593659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593696 : List Nat := [2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 4]
def baseStart_2593696 : Nat := 118140960795 + 2593696 * 2 ^ 59
def prefixEnd_2593696 : Nat := 4983230072969 + 3 ^ 40 * 2593696 * 2
def baseEnd_2593696 : Nat := 1331812719643989386171815

theorem tailTrace_2593696 : CollatzResearch.WordTrace tailWord_2593696 prefixEnd_2593696 1331812719643989386171815 := by
  unfold tailWord_2593696
  simp only [CollatzResearch.WordTrace]
  refine ⟨47299932405744917427712471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63066576540993223236949961 47299932405744917427712471)
  ·
    refine ⟨70949898608617376141568707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47299932405744917427712471 70949898608617376141568707)
    ·
      refine ⟨106424847912926064212353061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70949898608617376141568707 106424847912926064212353061)
      ·
        refine ⟨19954658983673637039816199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106424847912926064212353061 19954658983673637039816199)
        ·
          refine ⟨29931988475510455559724299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19954658983673637039816199 29931988475510455559724299)
          ·
            refine ⟨44897982713265683339586449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29931988475510455559724299 44897982713265683339586449)
            ·
              refine ⟨33673487034949262504689837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44897982713265683339586449 33673487034949262504689837)
              ·
                refine ⟨12627557638105973439258689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33673487034949262504689837 12627557638105973439258689)
                ·
                  refine ⟨9470668228579480079444017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12627557638105973439258689 9470668228579480079444017)
                  ·
                    refine ⟨7103001171434610059583013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9470668228579480079444017 7103001171434610059583013)
                    ·
                      refine ⟨1331812719643989386171815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7103001171434610059583013 1331812719643989386171815)
                      ·
                        rfl

theorem cell23_2593696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_2593696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2593696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2593696 prefixEnd_2593696 := by exact prefixLift 2593696
  have htrace : WordTrace (prefixWord ++ tailWord_2593696) baseStart_2593696 baseEnd_2593696 := by
    simpa [prefixWord, tailWord_2593696, baseEnd_2593696] using wordTrace_append hprefix tailTrace_2593696
  have hstable : (prefixWord ++ tailWord_2593696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593696).length < 2 ^ (prefixWord ++ tailWord_2593696).sum := by decide
  have hdescent : baseEnd_2593696 < baseStart_2593696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593743 : List Nat := [1, 1, 2, 1, 1, 6, 1, 1, 2, 5, 2]
def baseStart_2593743 : Nat := 118140960795 + 2593743 * 2 ^ 59
def prefixEnd_2593743 : Nat := 4983230072969 + 3 ^ 40 * 2593743 * 2
def baseEnd_2593743 : Nat := 1331836853234750702284099

theorem tailTrace_2593743 : CollatzResearch.WordTrace tailWord_2593743 prefixEnd_2593743 1331836853234750702284099 := by
  unfold tailWord_2593743
  simp only [CollatzResearch.WordTrace]
  refine ⟨94601579042319561882385883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63067719361546374588257255 94601579042319561882385883)
  ·
    refine ⟨141902368563479342823578825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94601579042319561882385883 141902368563479342823578825)
    ·
      refine ⟨106426776422609507117684119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141902368563479342823578825 106426776422609507117684119)
      ·
        refine ⟨159640164633914260676526179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106426776422609507117684119 159640164633914260676526179)
        ·
          refine ⟨239460246950871391014789269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159640164633914260676526179 239460246950871391014789269)
          ·
            refine ⟨11224699075822096453818247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 239460246950871391014789269 11224699075822096453818247)
            ·
              refine ⟨16837048613733144680727371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11224699075822096453818247 16837048613733144680727371)
              ·
                refine ⟨25255572920599717021091057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16837048613733144680727371 25255572920599717021091057)
                ·
                  refine ⟨18941679690449787765818293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25255572920599717021091057 18941679690449787765818293)
                  ·
                    refine ⟨1775782470979667603045465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18941679690449787765818293 1775782470979667603045465)
                    ·
                      refine ⟨1331836853234750702284099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1775782470979667603045465 1331836853234750702284099)
                      ·
                        rfl

theorem cell23_2593743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 5, 2].length) (baseStart_2593743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2593743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2593743 prefixEnd_2593743 := by exact prefixLift 2593743
  have htrace : WordTrace (prefixWord ++ tailWord_2593743) baseStart_2593743 baseEnd_2593743 := by
    simpa [prefixWord, tailWord_2593743, baseEnd_2593743] using wordTrace_append hprefix tailTrace_2593743
  have hstable : (prefixWord ++ tailWord_2593743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593743).length < 2 ^ (prefixWord ++ tailWord_2593743).sum := by decide
  have hdescent : baseEnd_2593743 < baseStart_2593743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593750 : List Nat := [5, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3]
def baseStart_2593750 : Nat := 118140960795 + 2593750 * 2 ^ 59
def prefixEnd_2593750 : Nat := 4983230072969 + 3 ^ 40 * 2593750 * 2
def baseEnd_2593750 : Nat := 1331840447599332174896567

theorem tailTrace_2593750 : CollatzResearch.WordTrace tailWord_2593750 prefixEnd_2593750 1331840447599332174896567 := by
  unfold tailWord_2593750
  simp only [CollatzResearch.WordTrace]
  refine ⟨5912614647080887629868169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63067889568862801385260469 5912614647080887629868169)
  ·
    refine ⟨4434460985310665722401127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5912614647080887629868169 4434460985310665722401127)
    ·
      refine ⟨6651691477965998583601691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4434460985310665722401127 6651691477965998583601691)
      ·
        refine ⟨9977537216948997875402537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6651691477965998583601691 9977537216948997875402537)
        ·
          refine ⟨7483152912711748406551903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9977537216948997875402537 7483152912711748406551903)
          ·
            refine ⟨11224729369067622609827855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7483152912711748406551903 11224729369067622609827855)
            ·
              refine ⟨16837094053601433914741783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11224729369067622609827855 16837094053601433914741783)
              ·
                refine ⟨25255641080402150872112675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16837094053601433914741783 25255641080402150872112675)
                ·
                  refine ⟨37883461620603226308169013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25255641080402150872112675 37883461620603226308169013)
                  ·
                    refine ⟨3551574526931552466390845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37883461620603226308169013 3551574526931552466390845)
                    ·
                      refine ⟨1331840447599332174896567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3551574526931552466390845 1331840447599332174896567)
                      ·
                        rfl

theorem cell23_2593750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_2593750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2593750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2593750 prefixEnd_2593750 := by exact prefixLift 2593750
  have htrace : WordTrace (prefixWord ++ tailWord_2593750) baseStart_2593750 baseEnd_2593750 := by
    simpa [prefixWord, tailWord_2593750, baseEnd_2593750] using wordTrace_append hprefix tailTrace_2593750
  have hstable : (prefixWord ++ tailWord_2593750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593750).length < 2 ^ (prefixWord ++ tailWord_2593750).sum := by decide
  have hdescent : baseEnd_2593750 < baseStart_2593750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593770 : List Nat := [3, 1, 3, 1, 2, 4, 1, 1, 2, 5]
def baseStart_2593770 : Nat := 118140960795 + 2593770 * 2 ^ 59
def prefixEnd_2593770 : Nat := 4983230072969 + 3 ^ 40 * 2593770 * 2
def baseEnd_2593770 : Nat := 443950239070807365548825

theorem tailTrace_2593770 : CollatzResearch.WordTrace tailWord_2593770 prefixEnd_2593770 443950239070807365548825 := by
  unfold tailWord_2593770
  simp only [CollatzResearch.WordTrace]
  refine ⟨23650640953305436373404691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63068375875481163662412509 23650640953305436373404691)
  ·
    refine ⟨35475961429958154560107037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23650640953305436373404691 35475961429958154560107037)
    ·
      refine ⟨13303485536234307960040139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35475961429958154560107037 13303485536234307960040139)
      ·
        refine ⟨19955228304351461940060209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13303485536234307960040139 19955228304351461940060209)
        ·
          refine ⟨14966421228263596455045157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19955228304351461940060209 14966421228263596455045157)
          ·
            refine ⟨2806203980299424335320967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14966421228263596455045157 2806203980299424335320967)
            ·
              refine ⟨4209305970449136502981451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2806203980299424335320967 4209305970449136502981451)
              ·
                refine ⟨6313958955673704754472177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4209305970449136502981451 6313958955673704754472177)
                ·
                  refine ⟨4735469216755278565854133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6313958955673704754472177 4735469216755278565854133)
                  ·
                    refine ⟨443950239070807365548825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4735469216755278565854133 443950239070807365548825)
                    ·
                      rfl

theorem cell23_2593770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_2593770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2593770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2593770 prefixEnd_2593770 := by exact prefixLift 2593770
  have htrace : WordTrace (prefixWord ++ tailWord_2593770) baseStart_2593770 baseEnd_2593770 := by
    simpa [prefixWord, tailWord_2593770, baseEnd_2593770] using wordTrace_append hprefix tailTrace_2593770
  have hstable : (prefixWord ++ tailWord_2593770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593770).length < 2 ^ (prefixWord ++ tailWord_2593770).sum := by decide
  have hdescent : baseEnd_2593770 < baseStart_2593770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593786 : List Nat := [3, 1, 1, 1, 1, 2, 1, 2, 1, 6, 4]
def baseStart_2593786 : Nat := 118140960795 + 2593786 * 2 ^ 59
def prefixEnd_2593786 : Nat := 4983230072969 + 3 ^ 40 * 2593786 * 2
def baseEnd_2593786 : Nat := 1331858932902894034046401

theorem tailTrace_2593786 : CollatzResearch.WordTrace tailWord_2593786 prefixEnd_2593786 1331858932902894034046401 := by
  unfold tailWord_2593786
  simp only [CollatzResearch.WordTrace]
  refine ⟨23650786845290945056550303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63068764920775853484134141 23650786845290945056550303)
  ·
    refine ⟨35476180267936417584825455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23650786845290945056550303 35476180267936417584825455)
    ·
      refine ⟨53214270401904626377238183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35476180267936417584825455 53214270401904626377238183)
      ·
        refine ⟨79821405602856939565857275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53214270401904626377238183 79821405602856939565857275)
        ·
          refine ⟨119732108404285409348785913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79821405602856939565857275 119732108404285409348785913)
          ·
            refine ⟨89799081303214057011589435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119732108404285409348785913 89799081303214057011589435)
            ·
              refine ⟨134698621954821085517384153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89799081303214057011589435 134698621954821085517384153)
              ·
                refine ⟨101023966466115814138038115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134698621954821085517384153 101023966466115814138038115)
                ·
                  refine ⟨151535949699173721207057173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101023966466115814138038115 151535949699173721207057173)
                  ·
                    refine ⟨7103247642148768181580805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 151535949699173721207057173 7103247642148768181580805)
                    ·
                      refine ⟨1331858932902894034046401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7103247642148768181580805 1331858932902894034046401)
                      ·
                        rfl

theorem cell23_2593786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 1, 6, 4].length) (baseStart_2593786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2593786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2593786 prefixEnd_2593786 := by exact prefixLift 2593786
  have htrace : WordTrace (prefixWord ++ tailWord_2593786) baseStart_2593786 baseEnd_2593786 := by
    simpa [prefixWord, tailWord_2593786, baseEnd_2593786] using wordTrace_append hprefix tailTrace_2593786
  have hstable : (prefixWord ++ tailWord_2593786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593786).length < 2 ^ (prefixWord ++ tailWord_2593786).sum := by decide
  have hdescent : baseEnd_2593786 < baseStart_2593786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593800 : List Nat := [2, 1, 3, 2, 1, 4, 2, 1, 3, 4]
def baseStart_2593800 : Nat := 118140960795 + 2593800 * 2 ^ 59
def prefixEnd_2593800 : Nat := 4983230072969 + 3 ^ 40 * 2593800 * 2
def baseEnd_2593800 : Nat := 443955373877352326423779

theorem tailTrace_2593800 : CollatzResearch.WordTrace tailWord_2593800 prefixEnd_2593800 443955373877352326423779 := by
  unfold tailWord_2593800
  simp only [CollatzResearch.WordTrace]
  refine ⟨47301829001556530308605427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63069105335408707078140569 47301829001556530308605427)
  ·
    refine ⟨70952743502334795462908141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47301829001556530308605427 70952743502334795462908141)
    ·
      refine ⟨26607278813375548298590553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70952743502334795462908141 26607278813375548298590553)
      ·
        refine ⟨19955459110031661223942915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26607278813375548298590553 19955459110031661223942915)
        ·
          refine ⟨29933188665047491835914373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19955459110031661223942915 29933188665047491835914373)
          ·
            refine ⟨5612472874696404719233945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29933188665047491835914373 5612472874696404719233945)
            ·
              refine ⟨4209354656022303539425459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5612472874696404719233945 4209354656022303539425459)
              ·
                refine ⟨6314031984033455309138189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4209354656022303539425459 6314031984033455309138189)
                ·
                  refine ⟨2367761994012545740926821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6314031984033455309138189 2367761994012545740926821)
                  ·
                    refine ⟨443955373877352326423779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2367761994012545740926821 443955373877352326423779)
                    ·
                      rfl

theorem cell23_2593800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 1, 3, 4].length) (baseStart_2593800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2593800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2593800 prefixEnd_2593800 := by exact prefixLift 2593800
  have htrace : WordTrace (prefixWord ++ tailWord_2593800) baseStart_2593800 baseEnd_2593800 := by
    simpa [prefixWord, tailWord_2593800, baseEnd_2593800] using wordTrace_append hprefix tailTrace_2593800
  have hstable : (prefixWord ++ tailWord_2593800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593800).length < 2 ^ (prefixWord ++ tailWord_2593800).sum := by decide
  have hdescent : baseEnd_2593800 < baseStart_2593800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593850 : List Nat := [3, 1, 1, 1, 3, 1, 3, 1, 4, 3, 2]
def baseStart_2593850 : Nat := 118140960795 + 2593850 * 2 ^ 59
def prefixEnd_2593850 : Nat := 4983230072969 + 3 ^ 40 * 2593850 * 2
def baseEnd_2593850 : Nat := 1331891795664781783646107

theorem tailTrace_2593850 : CollatzResearch.WordTrace tailWord_2593850 prefixEnd_2593850 1331891795664781783646107 := by
  unfold tailWord_2593850
  simp only [CollatzResearch.WordTrace]
  refine ⟨23651370413232979789132751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63070321101954612771020669 23651370413232979789132751)
  ·
    refine ⟨35477055619849469683699127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23651370413232979789132751 35477055619849469683699127)
    ·
      refine ⟨53215583429774204525548691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35477055619849469683699127 53215583429774204525548691)
      ·
        refine ⟨79823375144661306788323037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53215583429774204525548691 79823375144661306788323037)
        ·
          refine ⟨29933765679247990045621139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79823375144661306788323037 29933765679247990045621139)
          ·
            refine ⟨44900648518871985068431709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29933765679247990045621139 44900648518871985068431709)
            ·
              refine ⟨16837743194576994400661891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44900648518871985068431709 16837743194576994400661891)
              ·
                refine ⟨25256614791865491600992837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16837743194576994400661891 25256614791865491600992837)
                ·
                  refine ⟨4735615273474779675186157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25256614791865491600992837 4735615273474779675186157)
                  ·
                    refine ⟨1775855727553042378194809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4735615273474779675186157 1775855727553042378194809)
                    ·
                      refine ⟨1331891795664781783646107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1775855727553042378194809 1331891795664781783646107)
                      ·
                        rfl

theorem cell23_2593850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 4, 3, 2].length) (baseStart_2593850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2593850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2593850 prefixEnd_2593850 := by exact prefixLift 2593850
  have htrace : WordTrace (prefixWord ++ tailWord_2593850) baseStart_2593850 baseEnd_2593850 := by
    simpa [prefixWord, tailWord_2593850, baseEnd_2593850] using wordTrace_append hprefix tailTrace_2593850
  have hstable : (prefixWord ++ tailWord_2593850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593850).length < 2 ^ (prefixWord ++ tailWord_2593850).sum := by decide
  have hdescent : baseEnd_2593850 < baseStart_2593850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593890 : List Nat := [3, 3, 2, 2, 1, 1, 1, 1, 3, 6]
def baseStart_2593890 : Nat := 118140960795 + 2593890 * 2 ^ 59
def prefixEnd_2593890 : Nat := 4983230072969 + 3 ^ 40 * 2593890 * 2
def baseEnd_2593890 : Nat := 443970778296987209048641

theorem tailTrace_2593890 : CollatzResearch.WordTrace tailWord_2593890 prefixEnd_2593890 443970778296987209048641 := by
  unfold tailWord_2593890
  simp only [CollatzResearch.WordTrace]
  refine ⟨23651735143196751496996781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63071293715191337325324749 23651735143196751496996781)
  ·
    refine ⟨8869400678698781811373793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23651735143196751496996781 8869400678698781811373793)
    ·
      refine ⟨6652050509024086358530345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8869400678698781811373793 6652050509024086358530345)
      ·
        refine ⟨4989037881768064768897759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6652050509024086358530345 4989037881768064768897759)
        ·
          refine ⟨7483556822652097153346639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4989037881768064768897759 7483556822652097153346639)
          ·
            refine ⟨11225335233978145730019959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7483556822652097153346639 11225335233978145730019959)
            ·
              refine ⟨16838002850967218595029939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11225335233978145730019959 16838002850967218595029939)
              ·
                refine ⟨25257004276450827892544909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16838002850967218595029939 25257004276450827892544909)
                ·
                  refine ⟨9471376603669060459704341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25257004276450827892544909 9471376603669060459704341)
                  ·
                    refine ⟨443970778296987209048641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9471376603669060459704341 443970778296987209048641)
                    ·
                      rfl

theorem cell23_2593890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_2593890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2593890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2593890 prefixEnd_2593890 := by exact prefixLift 2593890
  have htrace : WordTrace (prefixWord ++ tailWord_2593890) baseStart_2593890 baseEnd_2593890 := by
    simpa [prefixWord, tailWord_2593890, baseEnd_2593890] using wordTrace_append hprefix tailTrace_2593890
  have hstable : (prefixWord ++ tailWord_2593890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593890).length < 2 ^ (prefixWord ++ tailWord_2593890).sum := by decide
  have hdescent : baseEnd_2593890 < baseStart_2593890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593897 : List Nat := [1, 2, 1, 1, 1, 7, 3, 1, 1, 1, 4]
def baseStart_2593897 : Nat := 118140960795 + 2593897 * 2 ^ 59
def prefixEnd_2593897 : Nat := 4983230072969 + 3 ^ 40 * 2593897 * 2
def baseEnd_2593897 : Nat := 1331915929255543099758391

theorem tailTrace_2593897 : CollatzResearch.WordTrace tailWord_2593897 prefixEnd_2593897 1331915929255543099758391 := by
  unfold tailWord_2593897
  simp only [CollatzResearch.WordTrace]
  refine ⟨94607195883761646183491945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63071463922507764122327963 94607195883761646183491945)
  ·
    refine ⟨70955396912821234637618959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94607195883761646183491945 70955396912821234637618959)
    ·
      refine ⟨106433095369231851956428439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70955396912821234637618959 106433095369231851956428439)
      ·
        refine ⟨159649643053847777934642659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106433095369231851956428439 159649643053847777934642659)
        ·
          refine ⟨239474464580771666901963989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159649643053847777934642659 239474464580771666901963989)
          ·
            refine ⟨5612682763611835943014781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 239474464580771666901963989 5612682763611835943014781)
            ·
              refine ⟨2104756036354438478630543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5612682763611835943014781 2104756036354438478630543)
              ·
                refine ⟨3157134054531657717945815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2104756036354438478630543 3157134054531657717945815)
                ·
                  refine ⟨4735701081797486576918723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3157134054531657717945815 4735701081797486576918723)
                  ·
                    refine ⟨7103551622696229865378085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4735701081797486576918723 7103551622696229865378085)
                    ·
                      refine ⟨1331915929255543099758391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7103551622696229865378085 1331915929255543099758391)
                      ·
                        rfl

theorem cell23_2593897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 1, 1, 1, 4].length) (baseStart_2593897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2593897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2593897 prefixEnd_2593897 := by exact prefixLift 2593897
  have htrace : WordTrace (prefixWord ++ tailWord_2593897) baseStart_2593897 baseEnd_2593897 := by
    simpa [prefixWord, tailWord_2593897, baseEnd_2593897] using wordTrace_append hprefix tailTrace_2593897
  have hstable : (prefixWord ++ tailWord_2593897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593897).length < 2 ^ (prefixWord ++ tailWord_2593897).sum := by decide
  have hdescent : baseEnd_2593897 < baseStart_2593897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593910 : List Nat := [5, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4]
def baseStart_2593910 : Nat := 118140960795 + 2593910 * 2 ^ 59
def prefixEnd_2593910 : Nat := 4983230072969 + 3 ^ 40 * 2593910 * 2
def baseEnd_2593910 : Nat := 1331922604504051548895831

theorem tailTrace_2593910 : CollatzResearch.WordTrace tailWord_2593910 prefixEnd_2593910 1331922604504051548895831 := by
  unfold tailWord_2593910
  simp only [CollatzResearch.WordTrace]
  refine ⟨5912979377044659337732199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63071780021809699602476789 5912979377044659337732199)
  ·
    refine ⟨8869469065566989006598299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5912979377044659337732199 8869469065566989006598299)
    ·
      refine ⟨13304203598350483509897449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8869469065566989006598299 13304203598350483509897449)
      ·
        refine ⟨9978152698762862632423087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13304203598350483509897449 9978152698762862632423087)
        ·
          refine ⟨14967229048144293948634631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9978152698762862632423087 14967229048144293948634631)
          ·
            refine ⟨22450843572216440922951947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14967229048144293948634631 22450843572216440922951947)
            ·
              refine ⟨33676265358324661384427921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22450843572216440922951947 33676265358324661384427921)
              ·
                refine ⟨25257199018743496038320941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33676265358324661384427921 25257199018743496038320941)
                ·
                  refine ⟨9471449632028811014370353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25257199018743496038320941 9471449632028811014370353)
                  ·
                    refine ⟨7103587224021608260777765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9471449632028811014370353 7103587224021608260777765)
                    ·
                      refine ⟨1331922604504051548895831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7103587224021608260777765 1331922604504051548895831)
                      ·
                        rfl

theorem cell23_2593910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_2593910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2593910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2593910 prefixEnd_2593910 := by exact prefixLift 2593910
  have htrace : WordTrace (prefixWord ++ tailWord_2593910) baseStart_2593910 baseEnd_2593910 := by
    simpa [prefixWord, tailWord_2593910, baseEnd_2593910] using wordTrace_append hprefix tailTrace_2593910
  have hstable : (prefixWord ++ tailWord_2593910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593910).length < 2 ^ (prefixWord ++ tailWord_2593910).sum := by decide
  have hdescent : baseEnd_2593910 < baseStart_2593910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593951 : List Nat := [1, 1, 2, 6, 2, 2, 2, 1, 1, 2, 3]
def baseStart_2593951 : Nat := 118140960795 + 2593951 * 2 ^ 59
def prefixEnd_2593951 : Nat := 4983230072969 + 3 ^ 40 * 2593951 * 2
def baseEnd_2593951 : Nat := 1331943657210885888483143

theorem tailTrace_2593951 : CollatzResearch.WordTrace tailWord_2593951 prefixEnd_2593951 1331943657210885888483143 := by
  unfold tailWord_2593951
  simp only [CollatzResearch.WordTrace]
  refine ⟨94609165425566013405957707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63072776950377342270638471 94609165425566013405957707)
  ·
    refine ⟨141913748138349020108936561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94609165425566013405957707 141913748138349020108936561)
    ·
      refine ⟨106435311103761765081702421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141913748138349020108936561 106435311103761765081702421)
      ·
        refine ⟨4989155207988832738204801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 106435311103761765081702421 4989155207988832738204801)
        ·
          refine ⟨3741866405991624553653601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4989155207988832738204801 3741866405991624553653601)
          ·
            refine ⟨2806399804493718415240201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3741866405991624553653601 2806399804493718415240201)
            ·
              refine ⟨2104799853370288811430151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2806399804493718415240201 2104799853370288811430151)
              ·
                refine ⟨3157199780055433217145227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2104799853370288811430151 3157199780055433217145227)
                ·
                  refine ⟨4735799670083149825717841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3157199780055433217145227 4735799670083149825717841)
                  ·
                    refine ⟨3551849752562362369288381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4735799670083149825717841 3551849752562362369288381)
                    ·
                      refine ⟨1331943657210885888483143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3551849752562362369288381 1331943657210885888483143)
                      ·
                        rfl

theorem cell23_2593951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_2593951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2593951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2593951 prefixEnd_2593951 := by exact prefixLift 2593951
  have htrace : WordTrace (prefixWord ++ tailWord_2593951) baseStart_2593951 baseEnd_2593951 := by
    simpa [prefixWord, tailWord_2593951, baseEnd_2593951] using wordTrace_append hprefix tailTrace_2593951
  have hstable : (prefixWord ++ tailWord_2593951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593951).length < 2 ^ (prefixWord ++ tailWord_2593951).sum := by decide
  have hdescent : baseEnd_2593951 < baseStart_2593951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2593980 : List Nat := [2, 2, 2, 3, 2, 1, 2, 1, 2, 6]
def baseStart_2593980 : Nat := 118140960795 + 2593980 * 2 ^ 59
def prefixEnd_2593980 : Nat := 4983230072969 + 3 ^ 40 * 2593980 * 2
def baseEnd_2593980 : Nat := 443986182716622091673503

theorem tailTrace_2593980 : CollatzResearch.WordTrace tailWord_2593980 prefixEnd_2593980 443986182716622091673503 := by
  unfold tailWord_2593980
  simp only [CollatzResearch.WordTrace]
  refine ⟨47305111571230475679381697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63073482094973967572508929 47305111571230475679381697)
  ·
    refine ⟨35478833678422856759536273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47305111571230475679381697 35478833678422856759536273)
    ·
      refine ⟨26609125258817142569652205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35478833678422856759536273 26609125258817142569652205)
      ·
        refine ⟨9978421972056428463619577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26609125258817142569652205 9978421972056428463619577)
        ·
          refine ⟨7483816479042321347714683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9978421972056428463619577 7483816479042321347714683)
          ·
            refine ⟨11225724718563482021572025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7483816479042321347714683 11225724718563482021572025)
            ·
              refine ⟨8419293538922611516179019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11225724718563482021572025 8419293538922611516179019)
              ·
                refine ⟨12628940308383917274268529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8419293538922611516179019 12628940308383917274268529)
                ·
                  refine ⟨9471705231287937955701397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12628940308383917274268529 9471705231287937955701397)
                  ·
                    refine ⟨443986182716622091673503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9471705231287937955701397 443986182716622091673503)
                    ·
                      rfl

theorem cell23_2593980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 2, 6].length) (baseStart_2593980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2593980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2593980 prefixEnd_2593980 := by exact prefixLift 2593980
  have htrace : WordTrace (prefixWord ++ tailWord_2593980) baseStart_2593980 baseEnd_2593980 := by
    simpa [prefixWord, tailWord_2593980, baseEnd_2593980] using wordTrace_append hprefix tailTrace_2593980
  have hstable : (prefixWord ++ tailWord_2593980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2593980).length < 2 ^ (prefixWord ++ tailWord_2593980).sum := by decide
  have hdescent : baseEnd_2593980 < baseStart_2593980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2593980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594020 : List Nat := [2, 3, 1, 1, 1, 2, 2, 1, 4, 3, 3]
def baseStart_2594020 : Nat := 118140960795 + 2594020 * 2 ^ 59
def prefixEnd_2594020 : Nat := 4983230072969 + 3 ^ 40 * 2594020 * 2
def baseEnd_2594020 : Nat := 1331979087376046118520325

theorem tailTrace_2594020 : CollatzResearch.WordTrace tailWord_2594020 prefixEnd_2594020 1331979087376046118520325 := by
  unfold tailWord_2594020
  simp only [CollatzResearch.WordTrace]
  refine ⟨47305841031158019095109757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63074454708210692126813009 47305841031158019095109757)
  ·
    refine ⟨17739690386684257160666159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47305841031158019095109757 17739690386684257160666159)
    ·
      refine ⟨26609535580026385740999239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17739690386684257160666159 26609535580026385740999239)
      ·
        refine ⟨39914303370039578611498859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26609535580026385740999239 39914303370039578611498859)
        ·
          refine ⟨59871455055059367917248289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39914303370039578611498859 59871455055059367917248289)
          ·
            refine ⟨44903591291294525937936217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59871455055059367917248289 44903591291294525937936217)
            ·
              refine ⟨33677693468470894453452163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44903591291294525937936217 33677693468470894453452163)
              ·
                refine ⟨50516540202706341680178245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33677693468470894453452163 50516540202706341680178245)
                ·
                  refine ⟨9471851288007439065033421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50516540202706341680178245 9471851288007439065033421)
                  ·
                    refine ⟨3551944233002789649387533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9471851288007439065033421 3551944233002789649387533)
                    ·
                      refine ⟨1331979087376046118520325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3551944233002789649387533 1331979087376046118520325)
                      ·
                        rfl

theorem cell23_2594020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 4, 3, 3].length) (baseStart_2594020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2594020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2594020 prefixEnd_2594020 := by exact prefixLift 2594020
  have htrace : WordTrace (prefixWord ++ tailWord_2594020) baseStart_2594020 baseEnd_2594020 := by
    simpa [prefixWord, tailWord_2594020, baseEnd_2594020] using wordTrace_append hprefix tailTrace_2594020
  have hstable : (prefixWord ++ tailWord_2594020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594020).length < 2 ^ (prefixWord ++ tailWord_2594020).sum := by decide
  have hdescent : baseEnd_2594020 < baseStart_2594020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594063 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 9]
def baseStart_2594063 : Nat := 118140960795 + 2594063 * 2 ^ 59
def prefixEnd_2594063 : Nat := 4983230072969 + 3 ^ 40 * 2594063 * 2
def baseEnd_2594063 : Nat := 1332001167044189450282627

theorem tailTrace_2594063 : CollatzResearch.WordTrace tailWord_2594063 prefixEnd_2594063 1332001167044189450282627 := by
  unfold tailWord_2594063
  simp only [CollatzResearch.WordTrace]
  refine ⟨94613250401160256534034843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63075500267440171022689895 94613250401160256534034843)
  ·
    refine ⟨141919875601740384801052265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94613250401160256534034843 141919875601740384801052265)
    ·
      refine ⟨106439906701305288600789199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141919875601740384801052265 106439906701305288600789199)
      ·
        refine ⟨159659860051957932901183799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106439906701305288600789199 159659860051957932901183799)
        ·
          refine ⟨239489790077936899351775699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159659860051957932901183799 239489790077936899351775699)
          ·
            refine ⟨359234685116905349027663549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239489790077936899351775699 359234685116905349027663549)
            ·
              refine ⟨134713006918839505885373831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 359234685116905349027663549 134713006918839505885373831)
              ·
                refine ⟨202069510378259258828060747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134713006918839505885373831 202069510378259258828060747)
                ·
                  refine ⟨303104265567388888242091121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 202069510378259258828060747 303104265567388888242091121)
                  ·
                    refine ⟨227328199175541666181568341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 303104265567388888242091121 227328199175541666181568341)
                    ·
                      refine ⟨1332001167044189450282627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 227328199175541666181568341 1332001167044189450282627)
                      ·
                        rfl

theorem cell23_2594063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 9].length) (baseStart_2594063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2594063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2594063 prefixEnd_2594063 := by exact prefixLift 2594063
  have htrace : WordTrace (prefixWord ++ tailWord_2594063) baseStart_2594063 baseEnd_2594063 := by
    simpa [prefixWord, tailWord_2594063, baseEnd_2594063] using wordTrace_append hprefix tailTrace_2594063
  have hstable : (prefixWord ++ tailWord_2594063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594063).length < 2 ^ (prefixWord ++ tailWord_2594063).sum := by decide
  have hdescent : baseEnd_2594063 < baseStart_2594063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594144 : List Nat := [2, 1, 1, 3, 4, 1, 1, 3, 3, 1, 3]
def baseStart_2594144 : Nat := 118140960795 + 2594144 * 2 ^ 59
def prefixEnd_2594144 : Nat := 4983230072969 + 3 ^ 40 * 2594144 * 2
def baseEnd_2594144 : Nat := 1332042758977203633369755

theorem tailTrace_2594144 : CollatzResearch.WordTrace tailWord_2594144 prefixEnd_2594144 1332042758977203633369755 := by
  unfold tailWord_2594144
  simp only [CollatzResearch.WordTrace]
  refine ⟨47308102356933403683866743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63077469809244538245155657 47308102356933403683866743)
  ·
    refine ⟨70962153535400105525800115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47308102356933403683866743 70962153535400105525800115)
    ·
      refine ⟨106443230303100158288700173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70962153535400105525800115 106443230303100158288700173)
      ·
        refine ⟨39916211363662559358262565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106443230303100158288700173 39916211363662559358262565)
        ·
          refine ⟨7484289630686729879674231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39916211363662559358262565 7484289630686729879674231)
          ·
            refine ⟨11226434446030094819511347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7484289630686729879674231 11226434446030094819511347)
            ·
              refine ⟨16839651669045142229267021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11226434446030094819511347 16839651669045142229267021)
              ·
                refine ⟨6314869375891928335975133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16839651669045142229267021 6314869375891928335975133)
                ·
                  refine ⟨2368076015959473125990675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6314869375891928335975133 2368076015959473125990675)
                  ·
                    refine ⟨3552114023939209688986013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2368076015959473125990675 3552114023939209688986013)
                    ·
                      refine ⟨1332042758977203633369755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3552114023939209688986013 1332042758977203633369755)
                      ·
                        rfl

theorem cell23_2594144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3, 3, 1, 3].length) (baseStart_2594144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2594144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2594144 prefixEnd_2594144 := by exact prefixLift 2594144
  have htrace : WordTrace (prefixWord ++ tailWord_2594144) baseStart_2594144 baseEnd_2594144 := by
    simpa [prefixWord, tailWord_2594144, baseEnd_2594144] using wordTrace_append hprefix tailTrace_2594144
  have hstable : (prefixWord ++ tailWord_2594144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594144).length < 2 ^ (prefixWord ++ tailWord_2594144).sum := by decide
  have hdescent : baseEnd_2594144 < baseStart_2594144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594167 : List Nat := [1, 1, 3, 1, 1, 2, 3, 1, 2, 6, 2]
def baseStart_2594167 : Nat := 118140960795 + 2594167 * 2 ^ 59
def prefixEnd_2594167 : Nat := 4983230072969 + 3 ^ 40 * 2594167 * 2
def baseEnd_2594167 : Nat := 1332054569032257043382149

theorem tailTrace_2594167 : CollatzResearch.WordTrace tailWord_2594167 prefixEnd_2594167 1332054569032257043382149 := by
  unfold tailWord_2594167
  simp only [CollatzResearch.WordTrace]
  refine ⟨94617043592783482295820755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63078029061855654863880503 94617043592783482295820755)
  ·
    refine ⟨141925565389175223443731133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94617043592783482295820755 141925565389175223443731133)
    ·
      refine ⟨53222087020940708791399175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141925565389175223443731133 53222087020940708791399175)
      ·
        refine ⟨79833130531411063187098763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53222087020940708791399175 79833130531411063187098763)
        ·
          refine ⟨119749695797116594780648145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79833130531411063187098763 119749695797116594780648145)
          ·
            refine ⟨89812271847837446085486109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119749695797116594780648145 89812271847837446085486109)
            ·
              refine ⟨33679601942939042282057291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89812271847837446085486109 33679601942939042282057291)
              ·
                refine ⟨50519402914408563423085937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33679601942939042282057291 50519402914408563423085937)
                ·
                  refine ⟨37889552185806422567314453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50519402914408563423085937 37889552185806422567314453)
                  ·
                    refine ⟨1776072758709676057842865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 37889552185806422567314453 1776072758709676057842865)
                    ·
                      refine ⟨1332054569032257043382149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1776072758709676057842865 1332054569032257043382149)
                      ·
                        rfl

theorem cell23_2594167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 6, 2].length) (baseStart_2594167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2594167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2594167 prefixEnd_2594167 := by exact prefixLift 2594167
  have htrace : WordTrace (prefixWord ++ tailWord_2594167) baseStart_2594167 baseEnd_2594167 := by
    simpa [prefixWord, tailWord_2594167, baseEnd_2594167] using wordTrace_append hprefix tailTrace_2594167
  have hstable : (prefixWord ++ tailWord_2594167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594167).length < 2 ^ (prefixWord ++ tailWord_2594167).sum := by decide
  have hdescent : baseEnd_2594167 < baseStart_2594167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594184 : List Nat := [2, 1, 3, 3, 1, 2, 2, 3, 1, 1, 4]
def baseStart_2594184 : Nat := 118140960795 + 2594184 * 2 ^ 59
def prefixEnd_2594184 : Nat := 4983230072969 + 3 ^ 40 * 2594184 * 2
def baseEnd_2594184 : Nat := 1332063298203383476869571

theorem tailTrace_2594184 : CollatzResearch.WordTrace tailWord_2594184 prefixEnd_2594184 1332063298203383476869571 := by
  unfold tailWord_2594184
  simp only [CollatzResearch.WordTrace]
  refine ⟨47308831816860947099594803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63078442422481262799459737 47308831816860947099594803)
  ·
    refine ⟨70963247725291420649392205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47308831816860947099594803 70963247725291420649392205)
    ·
      refine ⟨26611217896984282743522077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70963247725291420649392205 26611217896984282743522077)
      ·
        refine ⟨9979206711369106028820779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26611217896984282743522077 9979206711369106028820779)
        ·
          refine ⟨14968810067053659043231169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9979206711369106028820779 14968810067053659043231169)
          ·
            refine ⟨11226607550290244282423377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14968810067053659043231169 11226607550290244282423377)
            ·
              refine ⟨8419955662717683211817533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11226607550290244282423377 8419955662717683211817533)
              ·
                refine ⟨3157483373519131204431575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8419955662717683211817533 3157483373519131204431575)
                ·
                  refine ⟨4736225060278696806647363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3157483373519131204431575 4736225060278696806647363)
                  ·
                    refine ⟨7104337590418045209971045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4736225060278696806647363 7104337590418045209971045)
                    ·
                      refine ⟨1332063298203383476869571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7104337590418045209971045 1332063298203383476869571)
                      ·
                        rfl

theorem cell23_2594184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_2594184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2594184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2594184 prefixEnd_2594184 := by exact prefixLift 2594184
  have htrace : WordTrace (prefixWord ++ tailWord_2594184) baseStart_2594184 baseEnd_2594184 := by
    simpa [prefixWord, tailWord_2594184, baseEnd_2594184] using wordTrace_append hprefix tailTrace_2594184
  have hstable : (prefixWord ++ tailWord_2594184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594184).length < 2 ^ (prefixWord ++ tailWord_2594184).sum := by decide
  have hdescent : baseEnd_2594184 < baseStart_2594184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594187 : List Nat := [1, 1, 1, 1, 4, 3, 4, 1, 1, 1, 5]
def baseStart_2594187 : Nat := 118140960795 + 2594187 * 2 ^ 59
def prefixEnd_2594187 : Nat := 4983230072969 + 3 ^ 40 * 2594187 * 2
def baseEnd_2594187 : Nat := 1332064838645346965132057

theorem tailTrace_2594187 : CollatzResearch.WordTrace tailWord_2594187 prefixEnd_2594187 1332064838645346965132057 := by
  unfold tailWord_2594187
  simp only [CollatzResearch.WordTrace]
  refine ⟨94617773052711025711548815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63078515368474017141032543 94617773052711025711548815)
  ·
    refine ⟨141926659579066538567323223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94617773052711025711548815 141926659579066538567323223)
    ·
      refine ⟨212889989368599807850984835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141926659579066538567323223 212889989368599807850984835)
      ·
        refine ⟨319334984052899711776477253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212889989368599807850984835 319334984052899711776477253)
        ·
          refine ⟨59875309509918695958089485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 319334984052899711776477253 59875309509918695958089485)
          ·
            refine ⟨22453241066219510984283557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59875309509918695958089485 22453241066219510984283557)
            ·
              refine ⟨4209982699916158309553167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22453241066219510984283557 4209982699916158309553167)
              ·
                refine ⟨6314974049874237464329751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4209982699916158309553167 6314974049874237464329751)
                ·
                  refine ⟨9472461074811356196494627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6314974049874237464329751 9472461074811356196494627)
                  ·
                    refine ⟨14208691612217034294741941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9472461074811356196494627 14208691612217034294741941)
                    ·
                      refine ⟨1332064838645346965132057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14208691612217034294741941 1332064838645346965132057)
                      ·
                        rfl

theorem cell23_2594187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 1, 1, 1, 5].length) (baseStart_2594187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2594187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2594187 prefixEnd_2594187 := by exact prefixLift 2594187
  have htrace : WordTrace (prefixWord ++ tailWord_2594187) baseStart_2594187 baseEnd_2594187 := by
    simpa [prefixWord, tailWord_2594187, baseEnd_2594187] using wordTrace_append hprefix tailTrace_2594187
  have hstable : (prefixWord ++ tailWord_2594187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594187).length < 2 ^ (prefixWord ++ tailWord_2594187).sum := by decide
  have hdescent : baseEnd_2594187 < baseStart_2594187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594201 : List Nat := [1, 2, 1, 2, 1, 5, 3, 1, 3, 2, 2]
def baseStart_2594201 : Nat := 118140960795 + 2594201 * 2 ^ 59
def prefixEnd_2594201 : Nat := 4983230072969 + 3 ^ 40 * 2594201 * 2
def baseEnd_2594201 : Nat := 1332072027374509910356993

theorem tailTrace_2594201 : CollatzResearch.WordTrace tailWord_2594201 prefixEnd_2594201 1332072027374509910356993 := by
  unfold tailWord_2594201
  simp only [CollatzResearch.WordTrace]
  refine ⟨94618283674660306102558457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63078855783106870735038971 94618283674660306102558457)
  ·
    refine ⟨70963712755995229576918843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94618283674660306102558457 70963712755995229576918843)
    ·
      refine ⟨106445569133992844365378265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70963712755995229576918843 106445569133992844365378265)
      ·
        refine ⟨79834176850494633274033699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106445569133992844365378265 79834176850494633274033699)
        ·
          refine ⟨119751265275741949911050549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79834176850494633274033699 119751265275741949911050549)
          ·
            refine ⟨11226681119600807804160989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 119751265275741949911050549 11226681119600807804160989)
            ·
              refine ⟨4210005419850302926560371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11226681119600807804160989 4210005419850302926560371)
              ·
                refine ⟨6315008129775454389840557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4210005419850302926560371 6315008129775454389840557)
                ·
                  refine ⟨2368128048665795396190209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6315008129775454389840557 2368128048665795396190209)
                  ·
                    refine ⟨1776096036499346547142657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2368128048665795396190209 1776096036499346547142657)
                    ·
                      refine ⟨1332072027374509910356993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1776096036499346547142657 1332072027374509910356993)
                      ·
                        rfl

theorem cell23_2594201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 1, 3, 2, 2].length) (baseStart_2594201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2594201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2594201 prefixEnd_2594201 := by exact prefixLift 2594201
  have htrace : WordTrace (prefixWord ++ tailWord_2594201) baseStart_2594201 baseEnd_2594201 := by
    simpa [prefixWord, tailWord_2594201, baseEnd_2594201] using wordTrace_append hprefix tailTrace_2594201
  have hstable : (prefixWord ++ tailWord_2594201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594201).length < 2 ^ (prefixWord ++ tailWord_2594201).sum := by decide
  have hdescent : baseEnd_2594201 < baseStart_2594201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594207 : List Nat := [1, 1, 2, 5, 1, 3, 2, 8]
def baseStart_2594207 : Nat := 118140960795 + 2594207 * 2 ^ 59
def prefixEnd_2594207 : Nat := 4983230072969 + 3 ^ 40 * 2594207 * 2
def baseEnd_2594207 : Nat := 49336115120682847662295

theorem tailTrace_2594207 : CollatzResearch.WordTrace tailWord_2594207 prefixEnd_2594207 49336115120682847662295 := by
  unfold tailWord_2594207
  simp only [CollatzResearch.WordTrace]
  refine ⟨94618502512638569127276875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63079001675092379418184583 94618502512638569127276875)
  ·
    refine ⟨141927753768957853690915313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94618502512638569127276875 141927753768957853690915313)
    ·
      refine ⟨106445815326718390268186485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141927753768957853690915313 106445815326718390268186485)
      ·
        refine ⟨9979295186879849087642483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 106445815326718390268186485 9979295186879849087642483)
        ·
          refine ⟨14968942780319773631463725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9979295186879849087642483 14968942780319773631463725)
          ·
            refine ⟨5613353542619915111798897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14968942780319773631463725 5613353542619915111798897)
            ·
              refine ⟨4210015156964936333849173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5613353542619915111798897 4210015156964936333849173)
              ·
                refine ⟨49336115120682847662295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4210015156964936333849173 49336115120682847662295)
                ·
                  rfl

theorem cell23_2594207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 8].length) (baseStart_2594207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2594207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2594207 prefixEnd_2594207 := by exact prefixLift 2594207
  have htrace : WordTrace (prefixWord ++ tailWord_2594207) baseStart_2594207 baseEnd_2594207 := by
    simpa [prefixWord, tailWord_2594207, baseEnd_2594207] using wordTrace_append hprefix tailTrace_2594207
  have hstable : (prefixWord ++ tailWord_2594207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594207).length < 2 ^ (prefixWord ++ tailWord_2594207).sum := by decide
  have hdescent : baseEnd_2594207 < baseStart_2594207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594221 : List Nat := [1, 5, 2, 2, 1, 2, 1, 1, 3, 2, 3]
def baseStart_2594221 : Nat := 118140960795 + 2594221 * 2 ^ 59
def prefixEnd_2594221 : Nat := 4983230072969 + 3 ^ 40 * 2594221 * 2
def baseEnd_2594221 : Nat := 1332082296987599832106901

theorem tailTrace_2594221 : CollatzResearch.WordTrace tailWord_2594221 prefixEnd_2594221 1332082296987599832106901 := by
  unfold tailWord_2594221
  simp only [CollatzResearch.WordTrace]
  refine ⟨94619013134587849518286517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63079342089725233012191011 94619013134587849518286517)
  ·
    refine ⟨8870532481367610892339361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 94619013134587849518286517 8870532481367610892339361)
    ·
      refine ⟨6652899361025708169254521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8870532481367610892339361 6652899361025708169254521)
      ·
        refine ⟨4989674520769281126940891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6652899361025708169254521 4989674520769281126940891)
        ·
          refine ⟨7484511781153921690411337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4989674520769281126940891 7484511781153921690411337)
          ·
            refine ⟨5613383835865441267808503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7484511781153921690411337 5613383835865441267808503)
            ·
              refine ⟨8420075753798161901712755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5613383835865441267808503 8420075753798161901712755)
              ·
                refine ⟨12630113630697242852569133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8420075753798161901712755 12630113630697242852569133)
                ·
                  refine ⟨4736292611511466069713425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12630113630697242852569133 4736292611511466069713425)
                  ·
                    refine ⟨3552219458633599552285069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4736292611511466069713425 3552219458633599552285069)
                    ·
                      refine ⟨1332082296987599832106901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3552219458633599552285069 1332082296987599832106901)
                      ·
                        rfl

theorem cell23_2594221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_2594221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2594221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2594221 prefixEnd_2594221 := by exact prefixLift 2594221
  have htrace : WordTrace (prefixWord ++ tailWord_2594221) baseStart_2594221 baseEnd_2594221 := by
    simpa [prefixWord, tailWord_2594221, baseEnd_2594221] using wordTrace_append hprefix tailTrace_2594221
  have hstable : (prefixWord ++ tailWord_2594221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594221).length < 2 ^ (prefixWord ++ tailWord_2594221).sum := by decide
  have hdescent : baseEnd_2594221 < baseStart_2594221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594252 : List Nat := [2, 2, 1, 4, 2, 3, 2, 2, 1, 2, 2]
def baseStart_2594252 : Nat := 118140960795 + 2594252 * 2 ^ 59
def prefixEnd_2594252 : Nat := 4983230072969 + 3 ^ 40 * 2594252 * 2
def baseEnd_2594252 : Nat := 1332098214887889210819259

theorem tailTrace_2594252 : CollatzResearch.WordTrace tailWord_2594252 prefixEnd_2594252 1332098214887889210819259 := by
  unfold tailWord_2594252
  simp only [CollatzResearch.WordTrace]
  refine ⟨47310071898737770906332505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63080095864983694541776673 47310071898737770906332505)
  ·
    refine ⟨35482553924053328179749379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47310071898737770906332505 35482553924053328179749379)
    ·
      refine ⟨53223830886079992269624069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35482553924053328179749379 53223830886079992269624069)
      ·
        refine ⟨9979468291139998550554513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53223830886079992269624069 9979468291139998550554513)
        ·
          refine ⟨7484601218354998912915885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9979468291139998550554513 7484601218354998912915885)
          ·
            refine ⟨2806725456883124592343457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7484601218354998912915885 2806725456883124592343457)
            ·
              refine ⟨2105044092662343444257593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2806725456883124592343457 2105044092662343444257593)
              ·
                refine ⟨1578783069496757583193195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2105044092662343444257593 1578783069496757583193195)
                ·
                  refine ⟨2368174604245136374789793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1578783069496757583193195 2368174604245136374789793)
                  ·
                    refine ⟨1776130953183852281092345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2368174604245136374789793 1776130953183852281092345)
                    ·
                      refine ⟨1332098214887889210819259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1776130953183852281092345 1332098214887889210819259)
                      ·
                        rfl

theorem cell23_2594252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_2594252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2594252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2594252 prefixEnd_2594252 := by exact prefixLift 2594252
  have htrace : WordTrace (prefixWord ++ tailWord_2594252) baseStart_2594252 baseEnd_2594252 := by
    simpa [prefixWord, tailWord_2594252, baseEnd_2594252] using wordTrace_append hprefix tailTrace_2594252
  have hstable : (prefixWord ++ tailWord_2594252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594252).length < 2 ^ (prefixWord ++ tailWord_2594252).sum := by decide
  have hdescent : baseEnd_2594252 < baseStart_2594252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594302 : List Nat := [4, 2, 2, 3, 1, 2, 1, 2, 2, 1, 3]
def baseStart_2594302 : Nat := 118140960795 + 2594302 * 2 ^ 59
def prefixEnd_2594302 : Nat := 4983230072969 + 3 ^ 40 * 2594302 * 2
def baseEnd_2594302 : Nat := 1332123888920614015194029

theorem tailTrace_2594302 : CollatzResearch.WordTrace tailWord_2594302 prefixEnd_2594302 1332123888920614015194029 := by
  unfold tailWord_2594302
  simp only [CollatzResearch.WordTrace]
  refine ⟨11827745930911800043998145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63081311631529600234656773 11827745930911800043998145)
  ·
    refine ⟨8870809448183850032998609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11827745930911800043998145 8870809448183850032998609)
    ·
      refine ⟨6653107086137887524748957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8870809448183850032998609 6653107086137887524748957)
      ·
        refine ⟨2494915157301707821780859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6653107086137887524748957 2494915157301707821780859)
        ·
          refine ⟨3742372735952561732671289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2494915157301707821780859 3742372735952561732671289)
          ·
            refine ⟨2806779551964421299503467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3742372735952561732671289 2806779551964421299503467)
            ·
              refine ⟨4210169327946631949255201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2806779551964421299503467 4210169327946631949255201)
              ·
                refine ⟨3157626995959973961941401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4210169327946631949255201 3157626995959973961941401)
                ·
                  refine ⟨2368220246969980471456051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3157626995959973961941401 2368220246969980471456051)
                  ·
                    refine ⟨3552330370454970707184077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2368220246969980471456051 3552330370454970707184077)
                    ·
                      refine ⟨1332123888920614015194029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3552330370454970707184077 1332123888920614015194029)
                      ·
                        rfl

theorem cell23_2594302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_2594302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2594302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2594302 prefixEnd_2594302 := by exact prefixLift 2594302
  have htrace : WordTrace (prefixWord ++ tailWord_2594302) baseStart_2594302 baseEnd_2594302 := by
    simpa [prefixWord, tailWord_2594302, baseEnd_2594302] using wordTrace_append hprefix tailTrace_2594302
  have hstable : (prefixWord ++ tailWord_2594302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594302).length < 2 ^ (prefixWord ++ tailWord_2594302).sum := by decide
  have hdescent : baseEnd_2594302 < baseStart_2594302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594314 : List Nat := [3, 1, 2, 2, 2, 3, 2, 1, 7]
def baseStart_2594314 : Nat := 118140960795 + 2594314 * 2 ^ 59
def prefixEnd_2594314 : Nat := 4983230072969 + 3 ^ 40 * 2594314 * 2
def baseEnd_2594314 : Nat := 148014450076496440915997

theorem tailTrace_2594314 : CollatzResearch.WordTrace tailWord_2594314 prefixEnd_2594314 148014450076496440915997 := by
  unfold tailWord_2594314
  simp only [CollatzResearch.WordTrace]
  refine ⟨23655601280812731600355499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63081603415500617600947997 23655601280812731600355499)
  ·
    refine ⟨35483401921219097400533249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23655601280812731600355499 35483401921219097400533249)
    ·
      refine ⟨26612551440914323050399937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35483401921219097400533249 26612551440914323050399937)
      ·
        refine ⟨19959413580685742287799953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26612551440914323050399937 19959413580685742287799953)
        ·
          refine ⟨14969560185514306715849965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19959413580685742287799953 14969560185514306715849965)
          ·
            refine ⟨5613585069567865018443737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14969560185514306715849965 5613585069567865018443737)
            ·
              refine ⟨4210188802175898763832803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5613585069567865018443737 4210188802175898763832803)
              ·
                refine ⟨6315283203263848145749205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4210188802175898763832803 6315283203263848145749205)
                ·
                  refine ⟨148014450076496440915997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6315283203263848145749205 148014450076496440915997)
                  ·
                    rfl

theorem cell23_2594314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 1, 7].length) (baseStart_2594314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2594314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2594314 prefixEnd_2594314 := by exact prefixLift 2594314
  have htrace : WordTrace (prefixWord ++ tailWord_2594314) baseStart_2594314 baseEnd_2594314 := by
    simpa [prefixWord, tailWord_2594314, baseEnd_2594314] using wordTrace_append hprefix tailTrace_2594314
  have hstable : (prefixWord ++ tailWord_2594314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594314).length < 2 ^ (prefixWord ++ tailWord_2594314).sum := by decide
  have hdescent : baseEnd_2594314 < baseStart_2594314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594325 : List Nat := [1, 3, 2, 1, 3, 3, 3, 1, 2, 2, 2]
def baseStart_2594325 : Nat := 118140960795 + 2594325 * 2 ^ 59
def prefixEnd_2594325 : Nat := 4983230072969 + 3 ^ 40 * 2594325 * 2
def baseEnd_2594325 : Nat := 1332135698975667425206423

theorem tailTrace_2594325 : CollatzResearch.WordTrace tailWord_2594325 prefixEnd_2594325 1332135698975667425206423 := by
  unfold tailWord_2594325
  simp only [CollatzResearch.WordTrace]
  refine ⟨94622806326211075280072429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63081870884140716853381619 94622806326211075280072429)
  ·
    refine ⟨35483552372329153230027161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94622806326211075280072429 35483552372329153230027161)
    ·
      refine ⟨26612664279246864922520371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35483552372329153230027161 26612664279246864922520371)
      ·
        refine ⟨39918996418870297383780557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26612664279246864922520371 39918996418870297383780557)
        ·
          refine ⟨14969623657076361518917709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39918996418870297383780557 14969623657076361518917709)
          ·
            refine ⟨5613608871403635569594141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14969623657076361518917709 5613608871403635569594141)
            ·
              refine ⟨2105103326776363338597803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5613608871403635569594141 2105103326776363338597803)
              ·
                refine ⟨3157654990164545007896705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2105103326776363338597803 3157654990164545007896705)
                ·
                  refine ⟨2368241242623408755922529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3157654990164545007896705 2368241242623408755922529)
                  ·
                    refine ⟨1776180931967556566941897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2368241242623408755922529 1776180931967556566941897)
                    ·
                      refine ⟨1332135698975667425206423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1776180931967556566941897 1332135698975667425206423)
                      ·
                        rfl

theorem cell23_2594325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 1, 2, 2, 2].length) (baseStart_2594325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2594325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2594325 prefixEnd_2594325 := by exact prefixLift 2594325
  have htrace : WordTrace (prefixWord ++ tailWord_2594325) baseStart_2594325 baseEnd_2594325 := by
    simpa [prefixWord, tailWord_2594325, baseEnd_2594325] using wordTrace_append hprefix tailTrace_2594325
  have hstable : (prefixWord ++ tailWord_2594325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594325).length < 2 ^ (prefixWord ++ tailWord_2594325).sum := by decide
  have hdescent : baseEnd_2594325 < baseStart_2594325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594377 : List Nat := [1, 2, 1, 1, 2, 2, 1, 4, 2, 1, 6]
def baseStart_2594377 : Nat := 118140960795 + 2594377 * 2 ^ 59
def prefixEnd_2594377 : Nat := 4983230072969 + 3 ^ 40 * 2594377 * 2
def baseEnd_2594377 : Nat := 1332162399969701221756183

theorem tailTrace_2594377 : CollatzResearch.WordTrace tailWord_2594377 prefixEnd_2594377 1332162399969701221756183 := by
  unfold tailWord_2594377
  simp only [CollatzResearch.WordTrace]
  refine ⟨94624702922022688160965385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63083135281348458773976923 94624702922022688160965385)
  ·
    refine ⟨70968527191517016120724039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94624702922022688160965385 70968527191517016120724039)
    ·
      refine ⟨106452790787275524181086059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70968527191517016120724039 106452790787275524181086059)
      ·
        refine ⟨159679186180913286271629089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106452790787275524181086059 159679186180913286271629089)
        ·
          refine ⟨119759389635684964703721817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159679186180913286271629089 119759389635684964703721817)
          ·
            refine ⟨89819542226763723527791363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119759389635684964703721817 89819542226763723527791363)
            ·
              refine ⟨134729313340145585291687045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89819542226763723527791363 134729313340145585291687045)
              ·
                refine ⟨25261746251277297242191321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 134729313340145585291687045 25261746251277297242191321)
                ·
                  refine ⟨18946309688457972931643491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25261746251277297242191321 18946309688457972931643491)
                  ·
                    refine ⟨28419464532686959397465237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18946309688457972931643491 28419464532686959397465237)
                    ·
                      refine ⟨1332162399969701221756183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28419464532686959397465237 1332162399969701221756183)
                      ·
                        rfl

theorem cell23_2594377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 1, 6].length) (baseStart_2594377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2594377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2594377 prefixEnd_2594377 := by exact prefixLift 2594377
  have htrace : WordTrace (prefixWord ++ tailWord_2594377) baseStart_2594377 baseEnd_2594377 := by
    simpa [prefixWord, tailWord_2594377, baseEnd_2594377] using wordTrace_append hprefix tailTrace_2594377
  have hstable : (prefixWord ++ tailWord_2594377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594377).length < 2 ^ (prefixWord ++ tailWord_2594377).sum := by decide
  have hdescent : baseEnd_2594377 < baseStart_2594377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594384 : List Nat := [2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 3]
def baseStart_2594384 : Nat := 118140960795 + 2594384 * 2 ^ 59
def prefixEnd_2594384 : Nat := 4983230072969 + 3 ^ 40 * 2594384 * 2
def baseEnd_2594384 : Nat := 1332165994334282694368651

theorem tailTrace_2594384 : CollatzResearch.WordTrace tailWord_2594384 prefixEnd_2594384 1332165994334282694368651 := by
  unfold tailWord_2594384
  simp only [CollatzResearch.WordTrace]
  refine ⟨47312479116498664178235103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63083305488664885570980137 47312479116498664178235103)
  ·
    refine ⟨70968718674747996267352655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47312479116498664178235103 70968718674747996267352655)
    ·
      refine ⟨106453078012121994401028983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70968718674747996267352655 106453078012121994401028983)
      ·
        refine ⟨159679617018182991601543475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106453078012121994401028983 159679617018182991601543475)
        ·
          refine ⟨239519425527274487402315213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159679617018182991601543475 239519425527274487402315213)
          ·
            refine ⟨89819784572727932775868205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 239519425527274487402315213 89819784572727932775868205)
            ·
              refine ⟨33682419214772974790950577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89819784572727932775868205 33682419214772974790950577)
              ·
                refine ⟨25261814411079731093212933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33682419214772974790950577 25261814411079731093212933)
                ·
                  refine ⟨4736590202077449579977425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25261814411079731093212933 4736590202077449579977425)
                  ·
                    refine ⟨3552442651558087184983069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4736590202077449579977425 3552442651558087184983069)
                    ·
                      refine ⟨1332165994334282694368651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3552442651558087184983069 1332165994334282694368651)
                      ·
                        rfl

theorem cell23_2594384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 3].length) (baseStart_2594384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2594384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2594384 prefixEnd_2594384 := by exact prefixLift 2594384
  have htrace : WordTrace (prefixWord ++ tailWord_2594384) baseStart_2594384 baseEnd_2594384 := by
    simpa [prefixWord, tailWord_2594384, baseEnd_2594384] using wordTrace_append hprefix tailTrace_2594384
  have hstable : (prefixWord ++ tailWord_2594384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594384).length < 2 ^ (prefixWord ++ tailWord_2594384).sum := by decide
  have hdescent : baseEnd_2594384 < baseStart_2594384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594401 : List Nat := [1, 2, 3, 1, 1, 3, 4, 1, 2, 2, 3]
def baseStart_2594401 : Nat := 118140960795 + 2594401 * 2 ^ 59
def prefixEnd_2594401 : Nat := 4983230072969 + 3 ^ 40 * 2594401 * 2
def baseEnd_2594401 : Nat := 1332174723505409127856073

theorem tailTrace_2594401 : CollatzResearch.WordTrace tailWord_2594401 prefixEnd_2594401 1332174723505409127856073 := by
  unfold tailWord_2594401
  simp only [CollatzResearch.WordTrace]
  refine ⟨94625578273935740259839057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63083718849290493506559371 94625578273935740259839057)
  ·
    refine ⟨70969183705451805194879293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94625578273935740259839057 70969183705451805194879293)
    ·
      refine ⟨26613443889544426948079735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70969183705451805194879293 26613443889544426948079735)
      ·
        refine ⟨39920165834316640422119603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26613443889544426948079735 39920165834316640422119603)
        ·
          refine ⟨59880248751474960633179405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39920165834316640422119603 59880248751474960633179405)
          ·
            refine ⟨22455093281803110237442277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59880248751474960633179405 22455093281803110237442277)
            ·
              refine ⟨4210329990338083169520427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22455093281803110237442277 4210329990338083169520427)
              ·
                refine ⟨6315494985507124754280641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4210329990338083169520427 6315494985507124754280641)
                ·
                  refine ⟨4736621239130343565710481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6315494985507124754280641 4736621239130343565710481)
                  ·
                    refine ⟨3552465929347757674282861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4736621239130343565710481 3552465929347757674282861)
                    ·
                      refine ⟨1332174723505409127856073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3552465929347757674282861 1332174723505409127856073)
                      ·
                        rfl

theorem cell23_2594401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 1, 2, 2, 3].length) (baseStart_2594401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2594401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2594401 prefixEnd_2594401 := by exact prefixLift 2594401
  have htrace : WordTrace (prefixWord ++ tailWord_2594401) baseStart_2594401 baseEnd_2594401 := by
    simpa [prefixWord, tailWord_2594401, baseEnd_2594401] using wordTrace_append hprefix tailTrace_2594401
  have hstable : (prefixWord ++ tailWord_2594401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594401).length < 2 ^ (prefixWord ++ tailWord_2594401).sum := by decide
  have hdescent : baseEnd_2594401 < baseStart_2594401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594421 : List Nat := [1, 3, 4, 2, 1, 1, 1, 4, 6]
def baseStart_2594421 : Nat := 118140960795 + 2594421 * 2 ^ 59
def prefixEnd_2594421 : Nat := 4983230072969 + 3 ^ 40 * 2594421 * 2
def baseEnd_2594421 : Nat := 148020554790944338845109

theorem tailTrace_2594421 : CollatzResearch.WordTrace tailWord_2594421 prefixEnd_2594421 148020554790944338845109 := by
  unfold tailWord_2594421
  simp only [CollatzResearch.WordTrace]
  refine ⟨94626307733863283675567117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63084205155908855783711411 94626307733863283675567117)
  ·
    refine ⟨35484865400198731378337669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94626307733863283675567117 35484865400198731378337669)
    ·
      refine ⟨6653412262537262133438313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35484865400198731378337669 6653412262537262133438313)
      ·
        refine ⟨4990059196902946600078735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6653412262537262133438313 4990059196902946600078735)
        ·
          refine ⟨7485088795354419900118103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4990059196902946600078735 7485088795354419900118103)
          ·
            refine ⟨11227633193031629850177155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7485088795354419900118103 11227633193031629850177155)
            ·
              refine ⟨16841449789547444775265733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11227633193031629850177155 16841449789547444775265733)
              ·
                refine ⟨3157771835540145895362325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16841449789547444775265733 3157771835540145895362325)
                ·
                  refine ⟨148020554790944338845109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3157771835540145895362325 148020554790944338845109)
                  ·
                    rfl

theorem cell23_2594421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 4, 6].length) (baseStart_2594421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2594421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2594421 prefixEnd_2594421 := by exact prefixLift 2594421
  have htrace : WordTrace (prefixWord ++ tailWord_2594421) baseStart_2594421 baseEnd_2594421 := by
    simpa [prefixWord, tailWord_2594421, baseEnd_2594421] using wordTrace_append hprefix tailTrace_2594421
  have hstable : (prefixWord ++ tailWord_2594421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594421).length < 2 ^ (prefixWord ++ tailWord_2594421).sum := by decide
  have hdescent : baseEnd_2594421 < baseStart_2594421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594441 : List Nat := [1, 2, 1, 1, 4, 1, 2, 2, 4, 3, 2]
def baseStart_2594441 : Nat := 118140960795 + 2594441 * 2 ^ 59
def prefixEnd_2594441 : Nat := 4983230072969 + 3 ^ 40 * 2594441 * 2
def baseEnd_2594441 : Nat := 1332195262731588971355889

theorem tailTrace_2594441 : CollatzResearch.WordTrace tailWord_2594441 prefixEnd_2594441 1332195262731588971355889 := by
  unfold tailWord_2594441
  simp only [CollatzResearch.WordTrace]
  refine ⟨94627037193790827091295177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63084691462527218060863451 94627037193790827091295177)
  ·
    refine ⟨70970277895343120318471383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94627037193790827091295177 70970277895343120318471383)
    ·
      refine ⟨106455416843014680477707075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70970277895343120318471383 106455416843014680477707075)
      ·
        refine ⟨159683125264522020716560613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106455416843014680477707075 159683125264522020716560613)
        ·
          refine ⟨29940585987097878884355115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 159683125264522020716560613 29940585987097878884355115)
          ·
            refine ⟨44910878980646818326532673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29940585987097878884355115 44910878980646818326532673)
            ·
              refine ⟨33683159235485113744899505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44910878980646818326532673 33683159235485113744899505)
              ·
                refine ⟨25262369426613835308674629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33683159235485113744899505 25262369426613835308674629)
                ·
                  refine ⟨4736694267490094120376493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25262369426613835308674629 4736694267490094120376493)
                  ·
                    refine ⟨1776260350308785295141185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4736694267490094120376493 1776260350308785295141185)
                    ·
                      refine ⟨1332195262731588971355889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1776260350308785295141185 1332195262731588971355889)
                      ·
                        rfl

theorem cell23_2594441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 4, 3, 2].length) (baseStart_2594441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2594441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2594441 prefixEnd_2594441 := by exact prefixLift 2594441
  have htrace : WordTrace (prefixWord ++ tailWord_2594441) baseStart_2594441 baseEnd_2594441 := by
    simpa [prefixWord, tailWord_2594441, baseEnd_2594441] using wordTrace_append hprefix tailTrace_2594441
  have hstable : (prefixWord ++ tailWord_2594441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594441).length < 2 ^ (prefixWord ++ tailWord_2594441).sum := by decide
  have hdescent : baseEnd_2594441 < baseStart_2594441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594452 : List Nat := [2, 4, 2, 2, 3, 1, 1, 1, 2, 2, 3]
def baseStart_2594452 : Nat := 118140960795 + 2594452 * 2 ^ 59
def prefixEnd_2594452 : Nat := 4983230072969 + 3 ^ 40 * 2594452 * 2
def baseEnd_2594452 : Nat := 1332200911018788428318339

theorem tailTrace_2594452 : CollatzResearch.WordTrace tailWord_2594452 prefixEnd_2594452 1332200911018788428318339 := by
  unfold tailWord_2594452
  simp only [CollatzResearch.WordTrace]
  refine ⟨47313719198375487984972805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63084958931167317313297073 47313719198375487984972805)
  ·
    refine ⟨8871322349695403997182401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47313719198375487984972805 8871322349695403997182401)
    ·
      refine ⟨6653491762271552997886801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8871322349695403997182401 6653491762271552997886801)
      ·
        refine ⟨4990118821703664748415101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6653491762271552997886801 4990118821703664748415101)
        ·
          refine ⟨1871294558138874280655663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4990118821703664748415101 1871294558138874280655663)
          ·
            refine ⟨2806941837208311420983495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1871294558138874280655663 2806941837208311420983495)
            ·
              refine ⟨4210412755812467131475243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2806941837208311420983495 4210412755812467131475243)
              ·
                refine ⟨6315619133718700697212865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4210412755812467131475243 6315619133718700697212865)
                ·
                  refine ⟨4736714350289025522909649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6315619133718700697212865 4736714350289025522909649)
                  ·
                    refine ⟨3552535762716769142182237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4736714350289025522909649 3552535762716769142182237)
                    ·
                      refine ⟨1332200911018788428318339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3552535762716769142182237 1332200911018788428318339)
                      ·
                        rfl

theorem cell23_2594452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_2594452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2594452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2594452 prefixEnd_2594452 := by exact prefixLift 2594452
  have htrace : WordTrace (prefixWord ++ tailWord_2594452) baseStart_2594452 baseEnd_2594452 := by
    simpa [prefixWord, tailWord_2594452, baseEnd_2594452] using wordTrace_append hprefix tailTrace_2594452
  have hstable : (prefixWord ++ tailWord_2594452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594452).length < 2 ^ (prefixWord ++ tailWord_2594452).sum := by decide
  have hdescent : baseEnd_2594452 < baseStart_2594452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594465 : List Nat := [1, 2, 3, 3, 2, 1, 1, 5, 1, 1, 3]
def baseStart_2594465 : Nat := 118140960795 + 2594465 * 2 ^ 59
def prefixEnd_2594465 : Nat := 4983230072969 + 3 ^ 40 * 2594465 * 2
def baseEnd_2594465 : Nat := 1332207586267296877455779

theorem tailTrace_2594465 : CollatzResearch.WordTrace tailWord_2594465 prefixEnd_2594465 1332207586267296877455779 := by
  unfold tailWord_2594465
  simp only [CollatzResearch.WordTrace]
  refine ⟨94627912545703879190168849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63085275030469252793445899 94627912545703879190168849)
  ·
    refine ⟨70970934409277909392626637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94627912545703879190168849 70970934409277909392626637)
    ·
      refine ⟨26614100403479216022234989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70970934409277909392626637 26614100403479216022234989)
      ·
        refine ⟨9980287651304706008338121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26614100403479216022234989 9980287651304706008338121)
        ·
          refine ⟨7485215738478529506253591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9980287651304706008338121 7485215738478529506253591)
          ·
            refine ⟨11227823607717794259380387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7485215738478529506253591 11227823607717794259380387)
            ·
              refine ⟨16841735411576691389070581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11227823607717794259380387 16841735411576691389070581)
              ·
                refine ⟨1578912694835314817725367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16841735411576691389070581 1578912694835314817725367)
                ·
                  refine ⟨2368369042252972226588051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1578912694835314817725367 2368369042252972226588051)
                  ·
                    refine ⟨3552553563379458339882077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2368369042252972226588051 3552553563379458339882077)
                    ·
                      refine ⟨1332207586267296877455779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3552553563379458339882077 1332207586267296877455779)
                      ·
                        rfl

theorem cell23_2594465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_2594465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2594465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2594465 prefixEnd_2594465 := by exact prefixLift 2594465
  have htrace : WordTrace (prefixWord ++ tailWord_2594465) baseStart_2594465 baseEnd_2594465 := by
    simpa [prefixWord, tailWord_2594465, baseEnd_2594465] using wordTrace_append hprefix tailTrace_2594465
  have hstable : (prefixWord ++ tailWord_2594465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594465).length < 2 ^ (prefixWord ++ tailWord_2594465).sum := by decide
  have hdescent : baseEnd_2594465 < baseStart_2594465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594468 : List Nat := [2, 3, 1, 2, 2, 2, 4, 1, 1, 5]
def baseStart_2594468 : Nat := 118140960795 + 2594468 * 2 ^ 59
def prefixEnd_2594468 : Nat := 4983230072969 + 3 ^ 40 * 2594468 * 2
def baseEnd_2594468 : Nat := 444069708903086788572755

theorem tailTrace_2594468 : CollatzResearch.WordTrace tailWord_2594468 prefixEnd_2594468 444069708903086788572755 := by
  unfold tailWord_2594468
  simp only [CollatzResearch.WordTrace]
  refine ⟨47314010982346505351264029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63085347976462007135018705 47314010982346505351264029)
  ·
    refine ⟨17742754118379939506724011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47314010982346505351264029 17742754118379939506724011)
    ·
      refine ⟨26614131177569909260086017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17742754118379939506724011 26614131177569909260086017)
      ·
        refine ⟨19960598383177431945064513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26614131177569909260086017 19960598383177431945064513)
        ·
          refine ⟨14970448787383073958798385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19960598383177431945064513 14970448787383073958798385)
          ·
            refine ⟨11227836590537305469098789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14970448787383073958798385 11227836590537305469098789)
            ·
              refine ⟨2105219360725744775456023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11227836590537305469098789 2105219360725744775456023)
              ·
                refine ⟨3157829041088617163184035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2105219360725744775456023 3157829041088617163184035)
                ·
                  refine ⟨4736743561632925744776053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3157829041088617163184035 4736743561632925744776053)
                  ·
                    refine ⟨444069708903086788572755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4736743561632925744776053 444069708903086788572755)
                    ·
                      rfl

theorem cell23_2594468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 1, 1, 5].length) (baseStart_2594468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2594468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2594468 prefixEnd_2594468 := by exact prefixLift 2594468
  have htrace : WordTrace (prefixWord ++ tailWord_2594468) baseStart_2594468 baseEnd_2594468 := by
    simpa [prefixWord, tailWord_2594468, baseEnd_2594468] using wordTrace_append hprefix tailTrace_2594468
  have hstable : (prefixWord ++ tailWord_2594468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594468).length < 2 ^ (prefixWord ++ tailWord_2594468).sum := by decide
  have hdescent : baseEnd_2594468 < baseStart_2594468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594472 : List Nat := [2, 1, 7, 1, 1, 2, 1, 2, 6]
def baseStart_2594472 : Nat := 118140960795 + 2594472 * 2 ^ 59
def prefixEnd_2594472 : Nat := 4983230072969 + 3 ^ 40 * 2594472 * 2
def baseEnd_2594472 : Nat := 148023464514653150007583

theorem tailTrace_2594472 : CollatzResearch.WordTrace tailWord_2594472 prefixEnd_2594472 148023464514653150007583 := by
  unfold tailWord_2594472
  simp only [CollatzResearch.WordTrace]
  refine ⟨47314083928339259692836835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63085445237785679590449113 47314083928339259692836835)
  ·
    refine ⟨70971125892508889539255253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47314083928339259692836835 70971125892508889539255253)
    ·
      refine ⟨1663385763105677098576295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 70971125892508889539255253 1663385763105677098576295)
      ·
        refine ⟨2495078644658515647864443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1663385763105677098576295 2495078644658515647864443)
        ·
          refine ⟨3742617966987773471796665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2495078644658515647864443 3742617966987773471796665)
          ·
            refine ⟨2806963475240830103847499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3742617966987773471796665 2806963475240830103847499)
            ·
              refine ⟨4210445212861245155771249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2806963475240830103847499 4210445212861245155771249)
              ·
                refine ⟨3157833909645933866828437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4210445212861245155771249 3157833909645933866828437)
                ·
                  refine ⟨148023464514653150007583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3157833909645933866828437 148023464514653150007583)
                  ·
                    rfl

theorem cell23_2594472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 2, 6].length) (baseStart_2594472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2594472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2594472 prefixEnd_2594472 := by exact prefixLift 2594472
  have htrace : WordTrace (prefixWord ++ tailWord_2594472) baseStart_2594472 baseEnd_2594472 := by
    simpa [prefixWord, tailWord_2594472, baseEnd_2594472] using wordTrace_append hprefix tailTrace_2594472
  have hstable : (prefixWord ++ tailWord_2594472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594472).length < 2 ^ (prefixWord ++ tailWord_2594472).sum := by decide
  have hdescent : baseEnd_2594472 < baseStart_2594472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594502 : List Nat := [6, 1, 2, 1, 1, 2, 2, 2, 1, 5]
def baseStart_2594502 : Nat := 118140960795 + 2594502 * 2 ^ 59
def prefixEnd_2594502 : Nat := 4983230072969 + 3 ^ 40 * 2594502 * 2
def baseEnd_2594502 : Nat := 444075528350504410897703

theorem tailTrace_2594502 : CollatzResearch.WordTrace tailWord_2594502 prefixEnd_2594502 444075528350504410897703 := by
  unfold tailWord_2594502
  simp only [CollatzResearch.WordTrace]
  refine ⟨2957164438955307328414555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 63086174697713223006177173 2957164438955307328414555)
  ·
    refine ⟨4435746658432960992621833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2957164438955307328414555 4435746658432960992621833)
    ·
      refine ⟨3326809993824720744466375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4435746658432960992621833 3326809993824720744466375)
      ·
        refine ⟨4990214990737081116699563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3326809993824720744466375 4990214990737081116699563)
        ·
          refine ⟨7485322486105621675049345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4990214990737081116699563 7485322486105621675049345)
          ·
            refine ⟨5613991864579216256287009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7485322486105621675049345 5613991864579216256287009)
            ·
              refine ⟨4210493898434412192215257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5613991864579216256287009 4210493898434412192215257)
              ·
                refine ⟨3157870423825809144161443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4210493898434412192215257 3157870423825809144161443)
                ·
                  refine ⟨4736805635738713716242165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3157870423825809144161443 4736805635738713716242165)
                  ·
                    refine ⟨444075528350504410897703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4736805635738713716242165 444075528350504410897703)
                    ·
                      rfl

theorem cell23_2594502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_2594502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2594502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2594502 prefixEnd_2594502 := by exact prefixLift 2594502
  have htrace : WordTrace (prefixWord ++ tailWord_2594502) baseStart_2594502 baseEnd_2594502 := by
    simpa [prefixWord, tailWord_2594502, baseEnd_2594502] using wordTrace_append hprefix tailTrace_2594502
  have hstable : (prefixWord ++ tailWord_2594502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594502).length < 2 ^ (prefixWord ++ tailWord_2594502).sum := by decide
  have hdescent : baseEnd_2594502 < baseStart_2594502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594522 : List Nat := [3, 1, 1, 2, 2, 3, 3, 3, 1, 2, 2]
def baseStart_2594522 : Nat := 118140960795 + 2594522 * 2 ^ 59
def prefixEnd_2594522 : Nat := 4983230072969 + 3 ^ 40 * 2594522 * 2
def baseEnd_2594522 : Nat := 1332236854664603154443017

theorem tailTrace_2594522 : CollatzResearch.WordTrace tailWord_2594522 prefixEnd_2594522 1332236854664603154443017 := by
  unfold tailWord_2594522
  simp only [CollatzResearch.WordTrace]
  refine ⟨23657497876624344481248455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63086661004331585283329213 23657497876624344481248455)
  ·
    refine ⟨35486246814936516721872683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23657497876624344481248455 35486246814936516721872683)
    ·
      refine ⟨53229370222404775082809025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35486246814936516721872683 53229370222404775082809025)
      ·
        refine ⟨39922027666803581312106769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53229370222404775082809025 39922027666803581312106769)
        ·
          refine ⟨29941520750102685984080077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39922027666803581312106769 29941520750102685984080077)
          ·
            refine ⟨11228070281288507244030029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29941520750102685984080077 11228070281288507244030029)
            ·
              refine ⟨4210526355483190216511261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11228070281288507244030029 4210526355483190216511261)
              ·
                refine ⟨1578947383306196331191723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4210526355483190216511261 1578947383306196331191723)
                ·
                  refine ⟨2368421074959294496787585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1578947383306196331191723 2368421074959294496787585)
                  ·
                    refine ⟨1776315806219470872590689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2368421074959294496787585 1776315806219470872590689)
                    ·
                      refine ⟨1332236854664603154443017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1776315806219470872590689 1332236854664603154443017)
                      ·
                        rfl

theorem cell23_2594522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 3, 1, 2, 2].length) (baseStart_2594522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2594522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2594522 prefixEnd_2594522 := by exact prefixLift 2594522
  have htrace : WordTrace (prefixWord ++ tailWord_2594522) baseStart_2594522 baseEnd_2594522 := by
    simpa [prefixWord, tailWord_2594522, baseEnd_2594522] using wordTrace_append hprefix tailTrace_2594522
  have hstable : (prefixWord ++ tailWord_2594522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594522).length < 2 ^ (prefixWord ++ tailWord_2594522).sum := by decide
  have hdescent : baseEnd_2594522 < baseStart_2594522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594525 : List Nat := [1, 4, 3, 3, 1, 1, 2, 1, 1, 1, 5]
def baseStart_2594525 : Nat := 118140960795 + 2594525 * 2 ^ 59
def prefixEnd_2594525 : Nat := 4983230072969 + 3 ^ 40 * 2594525 * 2
def baseEnd_2594525 : Nat := 1332238395106566642705503

theorem tailTrace_2594525 : CollatzResearch.WordTrace tailWord_2594525 prefixEnd_2594525 1332238395106566642705503 := by
  unfold tailWord_2594525
  simp only [CollatzResearch.WordTrace]
  refine ⟨94630100925486509437353029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63086733950324339624902019 94630100925486509437353029)
  ·
    refine ⟨17743143923528720519503693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94630100925486509437353029 17743143923528720519503693)
    ·
      refine ⟨6653678971323270194813885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17743143923528720519503693 6653678971323270194813885)
      ·
        refine ⟨2495129614246226323055207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6653678971323270194813885 2495129614246226323055207)
        ·
          refine ⟨3742694421369339484582811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2495129614246226323055207 3742694421369339484582811)
          ·
            refine ⟨5614041632054009226874217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3742694421369339484582811 5614041632054009226874217)
            ·
              refine ⟨4210531224040506920155663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5614041632054009226874217 4210531224040506920155663)
              ·
                refine ⟨6315796836060760380233495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4210531224040506920155663 6315796836060760380233495)
                ·
                  refine ⟨9473695254091140570350243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6315796836060760380233495 9473695254091140570350243)
                  ·
                    refine ⟨14210542881136710855525365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9473695254091140570350243 14210542881136710855525365)
                    ·
                      refine ⟨1332238395106566642705503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14210542881136710855525365 1332238395106566642705503)
                      ·
                        rfl

theorem cell23_2594525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_2594525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2594525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2594525 prefixEnd_2594525 := by exact prefixLift 2594525
  have htrace : WordTrace (prefixWord ++ tailWord_2594525) baseStart_2594525 baseEnd_2594525 := by
    simpa [prefixWord, tailWord_2594525, baseEnd_2594525] using wordTrace_append hprefix tailTrace_2594525
  have hstable : (prefixWord ++ tailWord_2594525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594525).length < 2 ^ (prefixWord ++ tailWord_2594525).sum := by decide
  have hdescent : baseEnd_2594525 < baseStart_2594525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594538 : List Nat := [3, 1, 3, 1, 1, 1, 4, 1, 4, 1, 3]
def baseStart_2594538 : Nat := 118140960795 + 2594538 * 2 ^ 59
def prefixEnd_2594538 : Nat := 4983230072969 + 3 ^ 40 * 2594538 * 2
def baseEnd_2594538 : Nat := 1332245070355075091842943

theorem tailTrace_2594538 : CollatzResearch.WordTrace tailWord_2594538 prefixEnd_2594538 1332245070355075091842943 := by
  unfold tailWord_2594538
  simp only [CollatzResearch.WordTrace]
  refine ⟨23657643768609853164394067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63087050049626275105050845 23657643768609853164394067)
  ·
    refine ⟨35486465652914779746591101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23657643768609853164394067 35486465652914779746591101)
    ·
      refine ⟨13307424619843042404971663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35486465652914779746591101 13307424619843042404971663)
      ·
        refine ⟨19961136929764563607457495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13307424619843042404971663 19961136929764563607457495)
        ·
          refine ⟨29941705394646845411186243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19961136929764563607457495 29941705394646845411186243)
          ·
            refine ⟨44912558091970268116779365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29941705394646845411186243 44912558091970268116779365)
            ·
              refine ⟨8421104642244425271896131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44912558091970268116779365 8421104642244425271896131)
              ·
                refine ⟨12631656963366637907844197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8421104642244425271896131 12631656963366637907844197)
                ·
                  refine ⟨2368435680631244607720787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12631656963366637907844197 2368435680631244607720787)
                  ·
                    refine ⟨3552653520946866911581181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2368435680631244607720787 3552653520946866911581181)
                    ·
                      refine ⟨1332245070355075091842943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3552653520946866911581181 1332245070355075091842943)
                      ·
                        rfl

theorem cell23_2594538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 4, 1, 3].length) (baseStart_2594538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2594538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2594538 prefixEnd_2594538 := by exact prefixLift 2594538
  have htrace : WordTrace (prefixWord ++ tailWord_2594538) baseStart_2594538 baseEnd_2594538 := by
    simpa [prefixWord, tailWord_2594538, baseEnd_2594538] using wordTrace_append hprefix tailTrace_2594538
  have hstable : (prefixWord ++ tailWord_2594538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594538).length < 2 ^ (prefixWord ++ tailWord_2594538).sum := by decide
  have hdescent : baseEnd_2594538 < baseStart_2594538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594554 : List Nat := [3, 1, 1, 1, 1, 3, 1, 3, 1, 8]
def baseStart_2594554 : Nat := 118140960795 + 2594554 * 2 ^ 59
def prefixEnd_2594554 : Nat := 4983230072969 + 3 ^ 40 * 2594554 * 2
def baseEnd_2594554 : Nat := 444084428681849009747623

theorem tailTrace_2594554 : CollatzResearch.WordTrace tailWord_2594554 prefixEnd_2594554 444084428681849009747623 := by
  unfold tailWord_2594554
  simp only [CollatzResearch.WordTrace]
  refine ⟨23657789660595361847539679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63087439094920964926772477 23657789660595361847539679)
  ·
    refine ⟨35486684490893042771309519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23657789660595361847539679 35486684490893042771309519)
    ·
      refine ⟨53230026736339564156964279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35486684490893042771309519 53230026736339564156964279)
      ·
        refine ⟨79845040104509346235446419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53230026736339564156964279 79845040104509346235446419)
        ·
          refine ⟨119767560156764019353169629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79845040104509346235446419 119767560156764019353169629)
          ·
            refine ⟨44912835058786507257438611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119767560156764019353169629 44912835058786507257438611)
            ·
              refine ⟨67369252588179760886157917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44912835058786507257438611 67369252588179760886157917)
              ·
                refine ⟨25263469720567410332309219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67369252588179760886157917 25263469720567410332309219)
                ·
                  refine ⟨37895204580851115498463829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25263469720567410332309219 37895204580851115498463829)
                  ·
                    refine ⟨444084428681849009747623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 37895204580851115498463829 444084428681849009747623)
                    ·
                      rfl

theorem cell23_2594554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 1, 8].length) (baseStart_2594554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2594554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2594554 prefixEnd_2594554 := by exact prefixLift 2594554
  have htrace : WordTrace (prefixWord ++ tailWord_2594554) baseStart_2594554 baseEnd_2594554 := by
    simpa [prefixWord, tailWord_2594554, baseEnd_2594554] using wordTrace_append hprefix tailTrace_2594554
  have hstable : (prefixWord ++ tailWord_2594554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594554).length < 2 ^ (prefixWord ++ tailWord_2594554).sum := by decide
  have hdescent : baseEnd_2594554 < baseStart_2594554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594581 : List Nat := [1, 3, 2, 1, 2, 3, 2, 1, 2, 1, 5]
def baseStart_2594581 : Nat := 118140960795 + 2594581 * 2 ^ 59
def prefixEnd_2594581 : Nat := 4983230072969 + 3 ^ 40 * 2594581 * 2
def baseEnd_2594581 : Nat := 1332267150023218423605245

theorem tailTrace_2594581 : CollatzResearch.WordTrace tailWord_2594581 prefixEnd_2594581 1332267150023218423605245 := by
  unfold tailWord_2594581
  simp only [CollatzResearch.WordTrace]
  refine ⟨94632143413283631001391597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63088095608855754000927731 94632143413283631001391597)
  ·
    refine ⟨35487053779981361625521849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94632143413283631001391597 35487053779981361625521849)
    ·
      refine ⟨26615290334986021219141387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35487053779981361625521849 26615290334986021219141387)
      ·
        refine ⟨39922935502479031828712081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26615290334986021219141387 39922935502479031828712081)
        ·
          refine ⟨29942201626859273871534061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39922935502479031828712081 29942201626859273871534061)
          ·
            refine ⟨11228325610072227701825273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29942201626859273871534061 11228325610072227701825273)
            ·
              refine ⟨8421244207554170776368955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11228325610072227701825273 8421244207554170776368955)
              ·
                refine ⟨12631866311331256164553433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8421244207554170776368955 12631866311331256164553433)
                ·
                  refine ⟨9473899733498442123415075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12631866311331256164553433 9473899733498442123415075)
                  ·
                    refine ⟨14210849600247663185122613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9473899733498442123415075 14210849600247663185122613)
                    ·
                      refine ⟨1332267150023218423605245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14210849600247663185122613 1332267150023218423605245)
                      ·
                        rfl

theorem cell23_2594581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_2594581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2594581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2594581 prefixEnd_2594581 := by exact prefixLift 2594581
  have htrace : WordTrace (prefixWord ++ tailWord_2594581) baseStart_2594581 baseEnd_2594581 := by
    simpa [prefixWord, tailWord_2594581, baseEnd_2594581] using wordTrace_append hprefix tailTrace_2594581
  have hstable : (prefixWord ++ tailWord_2594581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594581).length < 2 ^ (prefixWord ++ tailWord_2594581).sum := by decide
  have hdescent : baseEnd_2594581 < baseStart_2594581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594590 : List Nat := [4, 3, 2, 2, 1, 2, 2, 2, 1, 2, 2]
def baseStart_2594590 : Nat := 118140960795 + 2594590 * 2 ^ 59
def prefixEnd_2594590 : Nat := 4983230072969 + 3 ^ 40 * 2594590 * 2
def baseEnd_2594590 : Nat := 1332271771349108888392705

theorem tailTrace_2594590 : CollatzResearch.WordTrace tailWord_2594590 prefixEnd_2594590 1332271771349108888392705 := by
  unfold tailWord_2594590
  simp only [CollatzResearch.WordTrace]
  refine ⟨11829058958781378192308653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63088314446834017025646149 11829058958781378192308653)
  ·
    refine ⟨4435897109543016822115745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11829058958781378192308653 4435897109543016822115745)
    ·
      refine ⟨3326922832157262616586809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4435897109543016822115745 3326922832157262616586809)
      ·
        refine ⟨2495192124117946962440107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3326922832157262616586809 2495192124117946962440107)
        ·
          refine ⟨3742788186176920443660161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2495192124117946962440107 3742788186176920443660161)
          ·
            refine ⟨2807091139632690332745121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3742788186176920443660161 2807091139632690332745121)
            ·
              refine ⟨2105318354724517749558841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2807091139632690332745121 2105318354724517749558841)
              ·
                refine ⟨1578988766043388312169131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2105318354724517749558841 1578988766043388312169131)
                ·
                  refine ⟨2368483149065082468253697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1578988766043388312169131 2368483149065082468253697)
                  ·
                    refine ⟨1776362361798811851190273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2368483149065082468253697 1776362361798811851190273)
                    ·
                      refine ⟨1332271771349108888392705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1776362361798811851190273 1332271771349108888392705)
                      ·
                        rfl

theorem cell23_2594590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_2594590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2594590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2594590 prefixEnd_2594590 := by exact prefixLift 2594590
  have htrace : WordTrace (prefixWord ++ tailWord_2594590) baseStart_2594590 baseEnd_2594590 := by
    simpa [prefixWord, tailWord_2594590, baseEnd_2594590] using wordTrace_append hprefix tailTrace_2594590
  have hstable : (prefixWord ++ tailWord_2594590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594590).length < 2 ^ (prefixWord ++ tailWord_2594590).sum := by decide
  have hdescent : baseEnd_2594590 < baseStart_2594590 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594591 : List Nat := [1, 1, 2, 4, 2, 1, 2, 2, 2, 2, 4]
def baseStart_2594591 : Nat := 118140960795 + 2594591 * 2 ^ 59
def prefixEnd_2594591 : Nat := 4983230072969 + 3 ^ 40 * 2594591 * 2
def baseEnd_2594591 : Nat := 1332272284829763384480199

theorem tailTrace_2594591 : CollatzResearch.WordTrace tailWord_2594591 prefixEnd_2594591 1332272284829763384480199 := by
  unfold tailWord_2594591
  simp only [CollatzResearch.WordTrace]
  refine ⟨94632508143247402709255627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63088338762164935139503751 94632508143247402709255627)
  ·
    refine ⟨141948762214871104063883441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94632508143247402709255627 141948762214871104063883441)
    ·
      refine ⟨106461571661153328047912581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141948762214871104063883441 106461571661153328047912581)
      ·
        refine ⟨19961544686466249008983609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106461571661153328047912581 19961544686466249008983609)
        ·
          refine ⟨14971158514849686756737707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19961544686466249008983609 14971158514849686756737707)
          ·
            refine ⟨22456737772274530135106561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14971158514849686756737707 22456737772274530135106561)
            ·
              refine ⟨16842553329205897601329921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22456737772274530135106561 16842553329205897601329921)
              ·
                refine ⟨12631914996904423200997441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16842553329205897601329921 12631914996904423200997441)
                ·
                  refine ⟨9473936247678317400748081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12631914996904423200997441 9473936247678317400748081)
                  ·
                    refine ⟨7105452185758738050561061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9473936247678317400748081 7105452185758738050561061)
                    ·
                      refine ⟨1332272284829763384480199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7105452185758738050561061 1332272284829763384480199)
                      ·
                        rfl

theorem cell23_2594591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_2594591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2594591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2594591 prefixEnd_2594591 := by exact prefixLift 2594591
  have htrace : WordTrace (prefixWord ++ tailWord_2594591) baseStart_2594591 baseEnd_2594591 := by
    simpa [prefixWord, tailWord_2594591, baseEnd_2594591] using wordTrace_append hprefix tailTrace_2594591
  have hstable : (prefixWord ++ tailWord_2594591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594591).length < 2 ^ (prefixWord ++ tailWord_2594591).sum := by decide
  have hdescent : baseEnd_2594591 < baseStart_2594591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594595 : List Nat := [1, 1, 1, 4, 2, 1, 3, 4, 2, 2, 2]
def baseStart_2594595 : Nat := 118140960795 + 2594595 * 2 ^ 59
def prefixEnd_2594595 : Nat := 4983230072969 + 3 ^ 40 * 2594595 * 2
def baseEnd_2594595 : Nat := 1332274338752381368830181

theorem tailTrace_2594595 : CollatzResearch.WordTrace tailWord_2594595 prefixEnd_2594595 1332274338752381368830181 := by
  unfold tailWord_2594595
  simp only [CollatzResearch.WordTrace]
  refine ⟨94632654035232911392401239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63088436023488607594934159 94632654035232911392401239)
  ·
    refine ⟨141948981052849367088601859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94632654035232911392401239 141948981052849367088601859)
    ·
      refine ⟨212923471579274050632902789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141948981052849367088601859 212923471579274050632902789)
      ·
        refine ⟨39923150921113884493669273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 212923471579274050632902789 39923150921113884493669273)
        ·
          refine ⟨29942363190835413370251955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39923150921113884493669273 29942363190835413370251955)
          ·
            refine ⟨44913544786253120055377933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29942363190835413370251955 44913544786253120055377933)
            ·
              refine ⟨16842579294844920020766725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44913544786253120055377933 16842579294844920020766725)
              ·
                refine ⟨3157983617783422503893761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16842579294844920020766725 3157983617783422503893761)
                ·
                  refine ⟨2368487713337566877920321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3157983617783422503893761 2368487713337566877920321)
                  ·
                    refine ⟨1776365785003175158440241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2368487713337566877920321 1776365785003175158440241)
                    ·
                      refine ⟨1332274338752381368830181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1776365785003175158440241 1332274338752381368830181)
                      ·
                        rfl

theorem cell23_2594595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 4, 2, 2, 2].length) (baseStart_2594595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2594595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2594595 prefixEnd_2594595 := by exact prefixLift 2594595
  have htrace : WordTrace (prefixWord ++ tailWord_2594595) baseStart_2594595 baseEnd_2594595 := by
    simpa [prefixWord, tailWord_2594595, baseEnd_2594595] using wordTrace_append hprefix tailTrace_2594595
  have hstable : (prefixWord ++ tailWord_2594595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594595).length < 2 ^ (prefixWord ++ tailWord_2594595).sum := by decide
  have hdescent : baseEnd_2594595 < baseStart_2594595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594612 : List Nat := [2, 5, 1, 1, 2, 2, 2, 1, 1, 4, 2]
def baseStart_2594612 : Nat := 118140960795 + 2594612 * 2 ^ 59
def prefixEnd_2594612 : Nat := 4983230072969 + 3 ^ 40 * 2594612 * 2
def baseEnd_2594612 : Nat := 1332283067923507802317603

theorem tailTrace_2594612 : CollatzResearch.WordTrace tailWord_2594612 prefixEnd_2594612 1332283067923507802317603 := by
  unfold tailWord_2594612
  simp only [CollatzResearch.WordTrace]
  refine ⟨47316637038085661647885045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63088849384114215530513393 47316637038085661647885045)
  ·
    refine ⟨4435934722320530779489223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47316637038085661647885045 4435934722320530779489223)
    ·
      refine ⟨6653902083480796169233835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4435934722320530779489223 6653902083480796169233835)
      ·
        refine ⟨9980853125221194253850753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6653902083480796169233835 9980853125221194253850753)
        ·
          refine ⟨7485639843915895690388065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9980853125221194253850753 7485639843915895690388065)
          ·
            refine ⟨5614229882936921767791049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7485639843915895690388065 5614229882936921767791049)
            ·
              refine ⟨4210672412202691325843287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5614229882936921767791049 4210672412202691325843287)
              ·
                refine ⟨6316008618304036988764931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4210672412202691325843287 6316008618304036988764931)
                ·
                  refine ⟨9474012927456055483147397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6316008618304036988764931 9474012927456055483147397)
                  ·
                    refine ⟨1776377423898010403090137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9474012927456055483147397 1776377423898010403090137)
                    ·
                      refine ⟨1332283067923507802317603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1776377423898010403090137 1332283067923507802317603)
                      ·
                        rfl

theorem cell23_2594612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_2594612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2594612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2594612 prefixEnd_2594612 := by exact prefixLift 2594612
  have htrace : WordTrace (prefixWord ++ tailWord_2594612) baseStart_2594612 baseEnd_2594612 := by
    simpa [prefixWord, tailWord_2594612, baseEnd_2594612] using wordTrace_append hprefix tailTrace_2594612
  have hstable : (prefixWord ++ tailWord_2594612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594612).length < 2 ^ (prefixWord ++ tailWord_2594612).sum := by decide
  have hdescent : baseEnd_2594612 < baseStart_2594612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594681 : List Nat := [1, 2, 1, 3, 2, 2, 1, 1, 2, 4, 4]
def baseStart_2594681 : Nat := 118140960795 + 2594681 * 2 ^ 59
def prefixEnd_2594681 : Nat := 4983230072969 + 3 ^ 40 * 2594681 * 2
def baseEnd_2594681 : Nat := 1332318498088668032354785

theorem tailTrace_2594681 : CollatzResearch.WordTrace tailWord_2594681 prefixEnd_2594681 1332318498088668032354785 := by
  unfold tailWord_2594681
  simp only [CollatzResearch.WordTrace]
  refine ⟨94635790712921348080031897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63090527141947565386687931 94635790712921348080031897)
  ·
    refine ⟨70976843034691011060023923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94635790712921348080031897 70976843034691011060023923)
    ·
      refine ⟨106465264552036516590035885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70976843034691011060023923 106465264552036516590035885)
      ·
        refine ⟨39924474207013693721263457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106465264552036516590035885 39924474207013693721263457)
        ·
          refine ⟨29943355655260270290947593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39924474207013693721263457 29943355655260270290947593)
          ·
            refine ⟨22457516741445202718210695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29943355655260270290947593 22457516741445202718210695)
            ·
              refine ⟨33686275112167804077316043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22457516741445202718210695 33686275112167804077316043)
              ·
                refine ⟨50529412668251706115974065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33686275112167804077316043 50529412668251706115974065)
                ·
                  refine ⟨37897059501188779586980549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50529412668251706115974065 37897059501188779586980549)
                  ·
                    refine ⟨7105698656472896172558853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37897059501188779586980549 7105698656472896172558853)
                    ·
                      refine ⟨1332318498088668032354785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7105698656472896172558853 1332318498088668032354785)
                      ·
                        rfl

theorem cell23_2594681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_2594681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2594681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2594681 prefixEnd_2594681 := by exact prefixLift 2594681
  have htrace : WordTrace (prefixWord ++ tailWord_2594681) baseStart_2594681 baseEnd_2594681 := by
    simpa [prefixWord, tailWord_2594681, baseEnd_2594681] using wordTrace_append hprefix tailTrace_2594681
  have hstable : (prefixWord ++ tailWord_2594681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594681).length < 2 ^ (prefixWord ++ tailWord_2594681).sum := by decide
  have hdescent : baseEnd_2594681 < baseStart_2594681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594688 : List Nat := [2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 3]
def baseStart_2594688 : Nat := 118140960795 + 2594688 * 2 ^ 59
def prefixEnd_2594688 : Nat := 4983230072969 + 3 ^ 40 * 2594688 * 2
def baseEnd_2594688 : Nat := 1332322092453249504967253

theorem tailTrace_2594688 : CollatzResearch.WordTrace tailWord_2594688 prefixEnd_2594688 1332322092453249504967253 := by
  unfold tailWord_2594688
  simp only [CollatzResearch.WordTrace]
  refine ⟨47318023011947994137768359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63090697349263992183691145 47318023011947994137768359)
  ·
    refine ⟨70977034517921991206652539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47318023011947994137768359 70977034517921991206652539)
    ·
      refine ⟨106465551776882986809978809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70977034517921991206652539 106465551776882986809978809)
      ·
        refine ⟨79849163832662240107484107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106465551776882986809978809 79849163832662240107484107)
        ·
          refine ⟨119773745748993360161226161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79849163832662240107484107 119773745748993360161226161)
          ·
            refine ⟨89830309311745020120919621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119773745748993360161226161 89830309311745020120919621)
            ·
              refine ⟨16843182995952191272672429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89830309311745020120919621 16843182995952191272672429)
              ·
                refine ⟨6316193623482071727252161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16843182995952191272672429 6316193623482071727252161)
                ·
                  refine ⟨4737145217611553795439121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6316193623482071727252161 4737145217611553795439121)
                  ·
                    refine ⟨3552858913208665346579341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4737145217611553795439121 3552858913208665346579341)
                    ·
                      refine ⟨1332322092453249504967253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3552858913208665346579341 1332322092453249504967253)
                      ·
                        rfl

theorem cell23_2594688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 3].length) (baseStart_2594688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2594688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2594688 prefixEnd_2594688 := by exact prefixLift 2594688
  have htrace : WordTrace (prefixWord ++ tailWord_2594688) baseStart_2594688 baseEnd_2594688 := by
    simpa [prefixWord, tailWord_2594688, baseEnd_2594688] using wordTrace_append hprefix tailTrace_2594688
  have hstable : (prefixWord ++ tailWord_2594688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594688).length < 2 ^ (prefixWord ++ tailWord_2594688).sum := by decide
  have hdescent : baseEnd_2594688 < baseStart_2594688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594691 : List Nat := [1, 1, 1, 3, 4, 2, 1, 2, 8]
def baseStart_2594691 : Nat := 118140960795 + 2594691 * 2 ^ 59
def prefixEnd_2594691 : Nat := 4983230072969 + 3 ^ 40 * 2594691 * 2
def baseEnd_2594691 : Nat := 148035959210579221469971

theorem tailTrace_2594691 : CollatzResearch.WordTrace tailWord_2594691 prefixEnd_2594691 148035959210579221469971 := by
  unfold tailWord_2594691
  simp only [CollatzResearch.WordTrace]
  refine ⟨94636155442885119787895927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63090770295256746525263951 94636155442885119787895927)
  ·
    refine ⟨141954233164327679681843891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94636155442885119787895927 141954233164327679681843891)
    ·
      refine ⟨212931349746491519522765837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141954233164327679681843891 212931349746491519522765837)
      ·
        refine ⟨79849256154934319821037189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 212931349746491519522765837 79849256154934319821037189)
        ·
          refine ⟨14971735529050184966444473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79849256154934319821037189 14971735529050184966444473)
          ·
            refine ⟨11228801646787638724833355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14971735529050184966444473 11228801646787638724833355)
            ·
              refine ⟨16843202470181458087250033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11228801646787638724833355 16843202470181458087250033)
              ·
                refine ⟨12632401852636093565437525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16843202470181458087250033 12632401852636093565437525)
                ·
                  refine ⟨148035959210579221469971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12632401852636093565437525 148035959210579221469971)
                  ·
                    rfl

theorem cell23_2594691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 8].length) (baseStart_2594691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2594691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2594691 prefixEnd_2594691 := by exact prefixLift 2594691
  have htrace : WordTrace (prefixWord ++ tailWord_2594691) baseStart_2594691 baseEnd_2594691 := by
    simpa [prefixWord, tailWord_2594691, baseEnd_2594691] using wordTrace_append hprefix tailTrace_2594691
  have hstable : (prefixWord ++ tailWord_2594691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594691).length < 2 ^ (prefixWord ++ tailWord_2594691).sum := by decide
  have hdescent : baseEnd_2594691 < baseStart_2594691 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594702 : List Nat := [4, 1, 1, 5, 1, 1, 1, 2, 2, 1, 4]
def baseStart_2594702 : Nat := 118140960795 + 2594702 * 2 ^ 59
def prefixEnd_2594702 : Nat := 4983230072969 + 3 ^ 40 * 2594702 * 2
def baseEnd_2594702 : Nat := 1332329281182412450192189

theorem tailTrace_2594702 : CollatzResearch.WordTrace tailWord_2594702 prefixEnd_2594702 1332329281182412450192189 := by
  unfold tailWord_2594702
  simp only [CollatzResearch.WordTrace]
  refine ⟨11829569580730658583318295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63091037763896845777697573 11829569580730658583318295)
  ·
    refine ⟨17744354371095987874977443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11829569580730658583318295 17744354371095987874977443)
    ·
      refine ⟨26616531556643981812466165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17744354371095987874977443 26616531556643981812466165)
      ·
        refine ⟨2495299833435373294918703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26616531556643981812466165 2495299833435373294918703)
        ·
          refine ⟨3742949750153059942378055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2495299833435373294918703 3742949750153059942378055)
          ·
            refine ⟨5614424625229589913567083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3742949750153059942378055 5614424625229589913567083)
            ·
              refine ⟨8421636937844384870350625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5614424625229589913567083 8421636937844384870350625)
              ·
                refine ⟨6316227703383288652762969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8421636937844384870350625 6316227703383288652762969)
                ·
                  refine ⟨4737170777537466489572227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6316227703383288652762969 4737170777537466489572227)
                  ·
                    refine ⟨7105756166306199734358341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4737170777537466489572227 7105756166306199734358341)
                    ·
                      refine ⟨1332329281182412450192189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7105756166306199734358341 1332329281182412450192189)
                      ·
                        rfl

theorem cell23_2594702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_2594702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2594702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2594702 prefixEnd_2594702 := by exact prefixLift 2594702
  have htrace : WordTrace (prefixWord ++ tailWord_2594702) baseStart_2594702 baseEnd_2594702 := by
    simpa [prefixWord, tailWord_2594702, baseEnd_2594702] using wordTrace_append hprefix tailTrace_2594702
  have hstable : (prefixWord ++ tailWord_2594702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594702).length < 2 ^ (prefixWord ++ tailWord_2594702).sum := by decide
  have hdescent : baseEnd_2594702 < baseStart_2594702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594708 : List Nat := [2, 4, 2, 1, 1, 2, 2, 1, 8]
def baseStart_2594708 : Nat := 118140960795 + 2594708 * 2 ^ 59
def prefixEnd_2594708 : Nat := 4983230072969 + 3 ^ 40 * 2594708 * 2
def baseEnd_2594708 : Nat := 148036929118482158524129

theorem tailTrace_2594708 : CollatzResearch.WordTrace tailWord_2594708 prefixEnd_2594708 148036929118482158524129 := by
  unfold tailWord_2594708
  simp only [CollatzResearch.WordTrace]
  refine ⟨47318387741911765845632389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63091183655882354460843185 47318387741911765845632389)
  ·
    refine ⟨8872197701608456096056073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47318387741911765845632389 8872197701608456096056073)
    ·
      refine ⟨6654148276206342072042055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8872197701608456096056073 6654148276206342072042055)
      ·
        refine ⟨9981222414309513108063083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6654148276206342072042055 9981222414309513108063083)
        ·
          refine ⟨14971833621464269662094625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9981222414309513108063083 14971833621464269662094625)
          ·
            refine ⟨11228875216098202246570969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14971833621464269662094625 11228875216098202246570969)
            ·
              refine ⟨8421656412073651684928227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11228875216098202246570969 8421656412073651684928227)
              ·
                refine ⟨12632484618110477527392341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8421656412073651684928227 12632484618110477527392341)
                ·
                  refine ⟨148036929118482158524129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12632484618110477527392341 148036929118482158524129)
                  ·
                    rfl

theorem cell23_2594708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 8].length) (baseStart_2594708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2594708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2594708 prefixEnd_2594708 := by exact prefixLift 2594708
  have htrace : WordTrace (prefixWord ++ tailWord_2594708) baseStart_2594708 baseEnd_2594708 := by
    simpa [prefixWord, tailWord_2594708, baseEnd_2594708] using wordTrace_append hprefix tailTrace_2594708
  have hstable : (prefixWord ++ tailWord_2594708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594708).length < 2 ^ (prefixWord ++ tailWord_2594708).sum := by decide
  have hdescent : baseEnd_2594708 < baseStart_2594708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594752 : List Nat := [2, 1, 1, 2, 3, 2, 2, 5, 1, 1, 3]
def baseStart_2594752 : Nat := 118140960795 + 2594752 * 2 ^ 59
def prefixEnd_2594752 : Nat := 4983230072969 + 3 ^ 40 * 2594752 * 2
def baseEnd_2594752 : Nat := 1332354955215137254566959

theorem tailTrace_2594752 : CollatzResearch.WordTrace tailWord_2594752 prefixEnd_2594752 1332354955215137254566959 := by
  unfold tailWord_2594752
  simp only [CollatzResearch.WordTrace]
  refine ⟨47319190147832063602933255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63092253530442751470577673 47319190147832063602933255)
  ·
    refine ⟨70978785221748095404399883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47319190147832063602933255 70978785221748095404399883)
    ·
      refine ⟨106468177832622143106599825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70978785221748095404399883 106468177832622143106599825)
      ·
        refine ⟨79851133374466607329949869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106468177832622143106599825 79851133374466607329949869)
        ·
          refine ⟨29944175015424977748731201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79851133374466607329949869 29944175015424977748731201)
          ·
            refine ⟨22458131261568733311548401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29944175015424977748731201 22458131261568733311548401)
            ·
              refine ⟨16843598446176549983661301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22458131261568733311548401 16843598446176549983661301)
              ·
                refine ⟨1579087354329051560968247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16843598446176549983661301 1579087354329051560968247)
                ·
                  refine ⟨2368631031493577341452371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1579087354329051560968247 2368631031493577341452371)
                  ·
                    refine ⟨3552946547240366012178557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2368631031493577341452371 3552946547240366012178557)
                    ·
                      refine ⟨1332354955215137254566959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3552946547240366012178557 1332354955215137254566959)
                      ·
                        rfl

theorem cell23_2594752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 5, 1, 1, 3].length) (baseStart_2594752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2594752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2594752 prefixEnd_2594752 := by exact prefixLift 2594752
  have htrace : WordTrace (prefixWord ++ tailWord_2594752) baseStart_2594752 baseEnd_2594752 := by
    simpa [prefixWord, tailWord_2594752, baseEnd_2594752] using wordTrace_append hprefix tailTrace_2594752
  have hstable : (prefixWord ++ tailWord_2594752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594752).length < 2 ^ (prefixWord ++ tailWord_2594752).sum := by decide
  have hdescent : baseEnd_2594752 < baseStart_2594752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594768 : List Nat := [2, 1, 1, 1, 1, 2, 4, 3, 4, 4]
def baseStart_2594768 : Nat := 118140960795 + 2594768 * 2 ^ 59
def prefixEnd_2594768 : Nat := 4983230072969 + 3 ^ 40 * 2594768 * 2
def baseEnd_2594768 : Nat := 444121056968536397322295

theorem tailTrace_2594768 : CollatzResearch.WordTrace tailWord_2594768 prefixEnd_2594768 444121056968536397322295 := by
  unfold tailWord_2594768
  simp only [CollatzResearch.WordTrace]
  refine ⟨47319481931803080969224479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63092642575737441292299305 47319481931803080969224479)
  ·
    refine ⟨70979222897704621453836719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47319481931803080969224479 70979222897704621453836719)
    ·
      refine ⟨106468834346556932180755079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70979222897704621453836719 106468834346556932180755079)
      ·
        refine ⟨159703251519835398271132619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106468834346556932180755079 159703251519835398271132619)
        ·
          refine ⟨239554877279753097406698929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159703251519835398271132619 239554877279753097406698929)
          ·
            refine ⟨179666157959814823055024197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 239554877279753097406698929 179666157959814823055024197)
            ·
              refine ⟨33687404617465279322817037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 179666157959814823055024197 33687404617465279322817037)
              ·
                refine ⟨12632776731549479746056389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33687404617465279322817037 12632776731549479746056389)
                ·
                  refine ⟨2368645637165527452385573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12632776731549479746056389 2368645637165527452385573)
                  ·
                    refine ⟨444121056968536397322295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2368645637165527452385573 444121056968536397322295)
                    ·
                      rfl

theorem cell23_2594768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 4, 4].length) (baseStart_2594768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2594768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2594768 prefixEnd_2594768 := by exact prefixLift 2594768
  have htrace : WordTrace (prefixWord ++ tailWord_2594768) baseStart_2594768 baseEnd_2594768 := by
    simpa [prefixWord, tailWord_2594768, baseEnd_2594768] using wordTrace_append hprefix tailTrace_2594768
  have hstable : (prefixWord ++ tailWord_2594768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594768).length < 2 ^ (prefixWord ++ tailWord_2594768).sum := by decide
  have hdescent : baseEnd_2594768 < baseStart_2594768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594785 : List Nat := [1, 2, 3, 1, 2, 1, 4, 3, 2, 4]
def baseStart_2594785 : Nat := 118140960795 + 2594785 * 2 ^ 59
def prefixEnd_2594785 : Nat := 4983230072969 + 3 ^ 40 * 2594785 * 2
def baseEnd_2594785 : Nat := 444123966692245208484769

theorem tailTrace_2594785 : CollatzResearch.WordTrace tailWord_2594785 prefixEnd_2594785 444123966692245208484769 := by
  unfold tailWord_2594785
  simp only [CollatzResearch.WordTrace]
  refine ⟨94639583904544573841817809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63093055936363049227878539 94639583904544573841817809)
  ·
    refine ⟨70979687928408430381363357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94639583904544573841817809 70979687928408430381363357)
    ·
      refine ⟨26617382973153161393011259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70979687928408430381363357 26617382973153161393011259)
      ·
        refine ⟨39926074459729742089516889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26617382973153161393011259 39926074459729742089516889)
        ·
          refine ⟨29944555844797306567137667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39926074459729742089516889 29944555844797306567137667)
          ·
            refine ⟨44916833767195959850706501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29944555844797306567137667 44916833767195959850706501)
            ·
              refine ⟨8421906331349242472007469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44916833767195959850706501 8421906331349242472007469)
              ·
                refine ⟨3158214874255965927002801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8421906331349242472007469 3158214874255965927002801)
                ·
                  refine ⟨2368661155691974445252101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3158214874255965927002801 2368661155691974445252101)
                  ·
                    refine ⟨444123966692245208484769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2368661155691974445252101 444123966692245208484769)
                    ·
                      rfl

theorem cell23_2594785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 3, 2, 4].length) (baseStart_2594785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2594785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2594785 prefixEnd_2594785 := by exact prefixLift 2594785
  have htrace : WordTrace (prefixWord ++ tailWord_2594785) baseStart_2594785 baseEnd_2594785 := by
    simpa [prefixWord, tailWord_2594785, baseEnd_2594785] using wordTrace_append hprefix tailTrace_2594785
  have hstable : (prefixWord ++ tailWord_2594785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594785).length < 2 ^ (prefixWord ++ tailWord_2594785).sum := by decide
  have hdescent : baseEnd_2594785 < baseStart_2594785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594806 : List Nat := [5, 1, 1, 1, 5, 1, 2, 1, 1, 5]
def baseStart_2594806 : Nat := 118140960795 + 2594806 * 2 ^ 59
def prefixEnd_2594806 : Nat := 4983230072969 + 3 ^ 40 * 2594806 * 2
def baseEnd_2594806 : Nat := 444127561056826681097237

theorem tailTrace_2594806 : CollatzResearch.WordTrace tailWord_2594806 prefixEnd_2594806 444127561056826681097237 := by
  unfold tailWord_2594806
  simp only [CollatzResearch.WordTrace]
  refine ⟨5915021864841780901770767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63093566558312329618888181 5915021864841780901770767)
  ·
    refine ⟨8872532797262671352656151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5915021864841780901770767 8872532797262671352656151)
    ·
      refine ⟨13308799195894007028984227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8872532797262671352656151 13308799195894007028984227)
      ·
        refine ⟨19963198793841010543476341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13308799195894007028984227 19963198793841010543476341)
        ·
          refine ⟨1871549886922594738450907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19963198793841010543476341 1871549886922594738450907)
          ·
            refine ⟨2807324830383892107676361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1871549886922594738450907 2807324830383892107676361)
            ·
              refine ⟨2105493622787919080757271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2807324830383892107676361 2105493622787919080757271)
              ·
                refine ⟨3158240434181878621135907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2105493622787919080757271 3158240434181878621135907)
                ·
                  refine ⟨4737360651272817931703861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3158240434181878621135907 4737360651272817931703861)
                  ·
                    refine ⟨444127561056826681097237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4737360651272817931703861 444127561056826681097237)
                    ·
                      rfl

theorem cell23_2594806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 1, 1, 5].length) (baseStart_2594806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2594806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2594806 prefixEnd_2594806 := by exact prefixLift 2594806
  have htrace : WordTrace (prefixWord ++ tailWord_2594806) baseStart_2594806 baseEnd_2594806 := by
    simpa [prefixWord, tailWord_2594806, baseEnd_2594806] using wordTrace_append hprefix tailTrace_2594806
  have hstable : (prefixWord ++ tailWord_2594806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594806).length < 2 ^ (prefixWord ++ tailWord_2594806).sum := by decide
  have hdescent : baseEnd_2594806 < baseStart_2594806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594809 : List Nat := [1, 2, 1, 3, 1, 4, 1, 5, 1, 2, 2]
def baseStart_2594809 : Nat := 118140960795 + 2594809 * 2 ^ 59
def prefixEnd_2594809 : Nat := 4983230072969 + 3 ^ 40 * 2594809 * 2
def baseEnd_2594809 : Nat := 1332384223612443531554197

theorem tailTrace_2594809 : CollatzResearch.WordTrace tailWord_2594809 prefixEnd_2594809 1332384223612443531554197 := by
  unfold tailWord_2594809
  simp only [CollatzResearch.WordTrace]
  refine ⟨94640459256457625940691481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63093639504305083960460987 94640459256457625940691481)
  ·
    refine ⟨70980344442343219455518611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94640459256457625940691481 70980344442343219455518611)
    ·
      refine ⟨106470516663514829183277917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70980344442343219455518611 106470516663514829183277917)
      ·
        refine ⟨39926443748818060943729219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106470516663514829183277917 39926443748818060943729219)
        ·
          refine ⟨59889665623227091415593829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39926443748818060943729219 59889665623227091415593829)
          ·
            refine ⟨11229312304355079640423843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59889665623227091415593829 11229312304355079640423843)
            ·
              refine ⟨16843968456532619460635765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11229312304355079640423843 16843968456532619460635765)
              ·
                refine ⟨1579122042799933074434603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16843968456532619460635765 1579122042799933074434603)
                ·
                  refine ⟨2368683064199899611651905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1579122042799933074434603 2368683064199899611651905)
                  ·
                    refine ⟨1776512298149924708738929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2368683064199899611651905 1776512298149924708738929)
                    ·
                      refine ⟨1332384223612443531554197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1776512298149924708738929 1332384223612443531554197)
                      ·
                        rfl

theorem cell23_2594809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 5, 1, 2, 2].length) (baseStart_2594809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2594809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2594809 prefixEnd_2594809 := by exact prefixLift 2594809
  have htrace : WordTrace (prefixWord ++ tailWord_2594809) baseStart_2594809 baseEnd_2594809 := by
    simpa [prefixWord, tailWord_2594809, baseEnd_2594809] using wordTrace_append hprefix tailTrace_2594809
  have hstable : (prefixWord ++ tailWord_2594809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594809).length < 2 ^ (prefixWord ++ tailWord_2594809).sum := by decide
  have hdescent : baseEnd_2594809 < baseStart_2594809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594835 : List Nat := [1, 1, 1, 2, 1, 4, 2, 1, 5, 3, 2]
def baseStart_2594835 : Nat := 118140960795 + 2594835 * 2 ^ 59
def prefixEnd_2594835 : Nat := 4983230072969 + 3 ^ 40 * 2594835 * 2
def baseEnd_2594835 : Nat := 1332397574109460429829077

theorem tailTrace_2594835 : CollatzResearch.WordTrace tailWord_2594835 prefixEnd_2594835 1332397574109460429829077 := by
  unfold tailWord_2594835
  simp only [CollatzResearch.WordTrace]
  refine ⟨94641407554363432381137959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63094271702908954920758639 94641407554363432381137959)
  ·
    refine ⟨141962111331545148571706939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94641407554363432381137959 141962111331545148571706939)
    ·
      refine ⟨212943166997317722857560409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141962111331545148571706939 212943166997317722857560409)
      ·
        refine ⟨159707375247988292143170307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212943166997317722857560409 159707375247988292143170307)
        ·
          refine ⟨239561062871982438214755461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159707375247988292143170307 239561062871982438214755461)
          ·
            refine ⟨44917699288496707165266649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 239561062871982438214755461 44917699288496707165266649)
            ·
              refine ⟨33688274466372530373949987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44917699288496707165266649 33688274466372530373949987)
              ·
                refine ⟨50532411699558795560924981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33688274466372530373949987 50532411699558795560924981)
                ·
                  refine ⟨4737413596833637083836717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50532411699558795560924981 4737413596833637083836717)
                  ·
                    refine ⟨1776530098812613906438769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4737413596833637083836717 1776530098812613906438769)
                    ·
                      refine ⟨1332397574109460429829077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1776530098812613906438769 1332397574109460429829077)
                      ·
                        rfl

theorem cell23_2594835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 5, 3, 2].length) (baseStart_2594835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2594835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2594835 prefixEnd_2594835 := by exact prefixLift 2594835
  have htrace : WordTrace (prefixWord ++ tailWord_2594835) baseStart_2594835 baseEnd_2594835 := by
    simpa [prefixWord, tailWord_2594835, baseEnd_2594835] using wordTrace_append hprefix tailTrace_2594835
  have hstable : (prefixWord ++ tailWord_2594835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594835).length < 2 ^ (prefixWord ++ tailWord_2594835).sum := by decide
  have hdescent : baseEnd_2594835 < baseStart_2594835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594836 : List Nat := [2, 4, 3, 2, 2, 1, 1, 1, 1, 6]
def baseStart_2594836 : Nat := 118140960795 + 2594836 * 2 ^ 59
def prefixEnd_2594836 : Nat := 4983230072969 + 3 ^ 40 * 2594836 * 2
def baseEnd_2594836 : Nat := 444132695863371641972191

theorem tailTrace_2594836 : CollatzResearch.WordTrace tailWord_2594836 prefixEnd_2594836 444132695863371641972191 := by
  unfold tailWord_2594836
  simp only [CollatzResearch.WordTrace]
  refine ⟨47320722013679904775962181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63094296018239873034616241 47320722013679904775962181)
  ·
    refine ⟨8872635377564982145492909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47320722013679904775962181 8872635377564982145492909)
    ·
      refine ⟨3327238266586868304559841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8872635377564982145492909 3327238266586868304559841)
      ·
        refine ⟨2495428699940151228419881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3327238266586868304559841 2495428699940151228419881)
        ·
          refine ⟨1871571524955113421314911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2495428699940151228419881 1871571524955113421314911)
          ·
            refine ⟨2807357287432670131972367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1871571524955113421314911 2807357287432670131972367)
            ·
              refine ⟨4211035931149005197958551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2807357287432670131972367 4211035931149005197958551)
              ·
                refine ⟨6316553896723507796937827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4211035931149005197958551 6316553896723507796937827)
                ·
                  refine ⟨9474830845085261695406741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6316553896723507796937827 9474830845085261695406741)
                  ·
                    refine ⟨444132695863371641972191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9474830845085261695406741 444132695863371641972191)
                    ·
                      rfl

theorem cell23_2594836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_2594836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2594836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2594836 prefixEnd_2594836 := by exact prefixLift 2594836
  have htrace : WordTrace (prefixWord ++ tailWord_2594836) baseStart_2594836 baseEnd_2594836 := by
    simpa [prefixWord, tailWord_2594836, baseEnd_2594836] using wordTrace_append hprefix tailTrace_2594836
  have hstable : (prefixWord ++ tailWord_2594836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594836).length < 2 ^ (prefixWord ++ tailWord_2594836).sum := by decide
  have hdescent : baseEnd_2594836 < baseStart_2594836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594839 : List Nat := [1, 1, 3, 5, 3, 1, 1, 1, 1, 2, 4]
def baseStart_2594839 : Nat := 118140960795 + 2594839 * 2 ^ 59
def prefixEnd_2594839 : Nat := 4983230072969 + 3 ^ 40 * 2594839 * 2
def baseEnd_2594839 : Nat := 1332399628032078414179059

theorem tailTrace_2594839 : CollatzResearch.WordTrace tailWord_2594839 prefixEnd_2594839 1332399628032078414179059 := by
  unfold tailWord_2594839
  simp only [CollatzResearch.WordTrace]
  refine ⟨94641553446348941064283571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63094368964232627376189047 94641553446348941064283571)
  ·
    refine ⟨141962330169523411596425357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94641553446348941064283571 141962330169523411596425357)
    ·
      refine ⟨53235873813571279348659509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141962330169523411596425357 53235873813571279348659509)
      ·
        refine ⟨4990863170022307438936829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53235873813571279348659509 4990863170022307438936829)
        ·
          refine ⟨1871573688758365289601311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4990863170022307438936829 1871573688758365289601311)
          ·
            refine ⟨2807360533137547934401967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1871573688758365289601311 2807360533137547934401967)
            ·
              refine ⟨4211040799706321901602951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2807360533137547934401967 4211040799706321901602951)
              ·
                refine ⟨6316561199559482852404427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4211040799706321901602951 6316561199559482852404427)
                ·
                  refine ⟨9474841799339224278606641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6316561199559482852404427 9474841799339224278606641)
                  ·
                    refine ⟨7106131349504418208954981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9474841799339224278606641 7106131349504418208954981)
                    ·
                      refine ⟨1332399628032078414179059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7106131349504418208954981 1332399628032078414179059)
                      ·
                        rfl

theorem cell23_2594839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_2594839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2594839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2594839 prefixEnd_2594839 := by exact prefixLift 2594839
  have htrace : WordTrace (prefixWord ++ tailWord_2594839) baseStart_2594839 baseEnd_2594839 := by
    simpa [prefixWord, tailWord_2594839, baseEnd_2594839] using wordTrace_append hprefix tailTrace_2594839
  have hstable : (prefixWord ++ tailWord_2594839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594839).length < 2 ^ (prefixWord ++ tailWord_2594839).sum := by decide
  have hdescent : baseEnd_2594839 < baseStart_2594839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594842 : List Nat := [3, 1, 1, 3, 1, 5, 1, 1, 1, 3, 3]
def baseStart_2594842 : Nat := 118140960795 + 2594842 * 2 ^ 59
def prefixEnd_2594842 : Nat := 4983230072969 + 3 ^ 40 * 2594842 * 2
def baseEnd_2594842 : Nat := 1332401168474041902441545

theorem tailTrace_2594842 : CollatzResearch.WordTrace tailWord_2594842 prefixEnd_2594842 1332401168474041902441545 := by
  unfold tailWord_2594842
  simp only [CollatzResearch.WordTrace]
  refine ⟨23660415716334518144160695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63094441910225381717761853 23660415716334518144160695)
  ·
    refine ⟨35490623574501777216241043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23660415716334518144160695 35490623574501777216241043)
    ·
      refine ⟨53235935361752665824361565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35490623574501777216241043 53235935361752665824361565)
      ·
        refine ⟨19963475760657249684135587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53235935361752665824361565 19963475760657249684135587)
        ·
          refine ⟨29945213640985874526203381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19963475760657249684135587 29945213640985874526203381)
          ·
            refine ⟨2807363778842425736831567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29945213640985874526203381 2807363778842425736831567)
            ·
              refine ⟨4211045668263638605247351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2807363778842425736831567 4211045668263638605247351)
              ·
                refine ⟨6316568502395457907871027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4211045668263638605247351 6316568502395457907871027)
                ·
                  refine ⟨9474852753593186861806541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6316568502395457907871027 9474852753593186861806541)
                  ·
                    refine ⟨3553069782597445073177453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9474852753593186861806541 3553069782597445073177453)
                    ·
                      refine ⟨1332401168474041902441545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3553069782597445073177453 1332401168474041902441545)
                      ·
                        rfl

theorem cell23_2594842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_2594842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2594842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2594842 prefixEnd_2594842 := by exact prefixLift 2594842
  have htrace : WordTrace (prefixWord ++ tailWord_2594842) baseStart_2594842 baseEnd_2594842 := by
    simpa [prefixWord, tailWord_2594842, baseEnd_2594842] using wordTrace_append hprefix tailTrace_2594842
  have hstable : (prefixWord ++ tailWord_2594842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594842).length < 2 ^ (prefixWord ++ tailWord_2594842).sum := by decide
  have hdescent : baseEnd_2594842 < baseStart_2594842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594888 : List Nat := [2, 1, 3, 1, 1, 1, 2, 5, 7]
def baseStart_2594888 : Nat := 118140960795 + 2594888 * 2 ^ 59
def prefixEnd_2594888 : Nat := 4983230072969 + 3 ^ 40 * 2594888 * 2
def baseEnd_2594888 : Nat := 148047198731572080274037

theorem tailTrace_2594888 : CollatzResearch.WordTrace tailWord_2594888 prefixEnd_2594888 148047198731572080274037 := by
  unfold tailWord_2594888
  simp only [CollatzResearch.WordTrace]
  refine ⟨47321670311585711216408659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63095560415447614955211545 47321670311585711216408659)
  ·
    refine ⟨70982505467378566824612989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47321670311585711216408659 70982505467378566824612989)
    ·
      refine ⟨26618439550266962559229871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70982505467378566824612989 26618439550266962559229871)
      ·
        refine ⟨39927659325400443838844807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26618439550266962559229871 39927659325400443838844807)
        ·
          refine ⟨59891488988100665758267211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39927659325400443838844807 59891488988100665758267211)
          ·
            refine ⟨89837233482150998637400817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59891488988100665758267211 89837233482150998637400817)
            ·
              refine ⟨67377925111613248978050613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89837233482150998637400817 67377925111613248978050613)
              ·
                refine ⟨6316680479213742091692245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67377925111613248978050613 6316680479213742091692245)
                ·
                  refine ⟨148047198731572080274037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6316680479213742091692245 148047198731572080274037)
                  ·
                    rfl

theorem cell23_2594888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5, 7].length) (baseStart_2594888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2594888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2594888 prefixEnd_2594888 := by exact prefixLift 2594888
  have htrace : WordTrace (prefixWord ++ tailWord_2594888) baseStart_2594888 baseEnd_2594888 := by
    simpa [prefixWord, tailWord_2594888, baseEnd_2594888] using wordTrace_append hprefix tailTrace_2594888
  have hstable : (prefixWord ++ tailWord_2594888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594888).length < 2 ^ (prefixWord ++ tailWord_2594888).sum := by decide
  have hdescent : baseEnd_2594888 < baseStart_2594888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594935 : List Nat := [1, 1, 3, 1, 1, 5, 2, 2, 2, 5]
def baseStart_2594935 : Nat := 118140960795 + 2594935 * 2 ^ 59
def prefixEnd_2594935 : Nat := 4983230072969 + 3 ^ 40 * 2594935 * 2
def baseEnd_2594935 : Nat := 444149640724970012859539

theorem tailTrace_2594935 : CollatzResearch.WordTrace tailWord_2594935 prefixEnd_2594935 444149640724970012859539 := by
  unfold tailWord_2594935
  simp only [CollatzResearch.WordTrace]
  refine ⟨94645054854001149459778259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63096703236000766306518839 94645054854001149459778259)
  ·
    refine ⟨141967582281001724189667389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94645054854001149459778259 141967582281001724189667389)
    ·
      refine ⟨53237843355375646571125271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141967582281001724189667389 53237843355375646571125271)
      ·
        refine ⟨79856765033063469856687907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53237843355375646571125271 79856765033063469856687907)
        ·
          refine ⟨119785147549595204785031861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79856765033063469856687907 119785147549595204785031861)
          ·
            refine ⟨11229857582774550448596737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 119785147549595204785031861 11229857582774550448596737)
            ·
              refine ⟨8422393187080912836447553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11229857582774550448596737 8422393187080912836447553)
              ·
                refine ⟨6316794890310684627335665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8422393187080912836447553 6316794890310684627335665)
                ·
                  refine ⟨4737596167733013470501749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6316794890310684627335665 4737596167733013470501749)
                  ·
                    refine ⟨444149640724970012859539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4737596167733013470501749 444149640724970012859539)
                    ·
                      rfl

theorem cell23_2594935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2, 2, 5].length) (baseStart_2594935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2594935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2594935 prefixEnd_2594935 := by exact prefixLift 2594935
  have htrace : WordTrace (prefixWord ++ tailWord_2594935) baseStart_2594935 baseEnd_2594935 := by
    simpa [prefixWord, tailWord_2594935, baseEnd_2594935] using wordTrace_append hprefix tailTrace_2594935
  have hstable : (prefixWord ++ tailWord_2594935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594935).length < 2 ^ (prefixWord ++ tailWord_2594935).sum := by decide
  have hdescent : baseEnd_2594935 < baseStart_2594935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594972 : List Nat := [2, 2, 3, 2, 1, 1, 1, 2, 1, 6, 2]
def baseStart_2594972 : Nat := 118140960795 + 2594972 * 2 ^ 59
def prefixEnd_2594972 : Nat := 4983230072969 + 3 ^ 40 * 2594972 * 2
def baseEnd_2594972 : Nat := 1332467920959126393815947

theorem tailTrace_2594972 : CollatzResearch.WordTrace tailWord_2594972 prefixEnd_2594972 1332467920959126393815947 := by
  unfold tailWord_2594972
  simp only [CollatzResearch.WordTrace]
  refine ⟨47323202177433552389437585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63097602903244736519250113 47323202177433552389437585)
  ·
    refine ⟨35492401633075164292078189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47323202177433552389437585 35492401633075164292078189)
    ·
      refine ⟨13309650612403186609529321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35492401633075164292078189 13309650612403186609529321)
      ·
        refine ⟨9982237959302389957146991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13309650612403186609529321 9982237959302389957146991)
        ·
          refine ⟨14973356938953584935720487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9982237959302389957146991 14973356938953584935720487)
          ·
            refine ⟨22460035408430377403580731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14973356938953584935720487 22460035408430377403580731)
            ·
              refine ⟨33690053112645566105371097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22460035408430377403580731 33690053112645566105371097)
              ·
                refine ⟨25267539834484174579028323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33690053112645566105371097 25267539834484174579028323)
                ·
                  refine ⟨37901309751726261868542485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25267539834484174579028323 37901309751726261868542485)
                  ·
                    refine ⟨1776623894612168525087929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 37901309751726261868542485 1776623894612168525087929)
                    ·
                      refine ⟨1332467920959126393815947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1776623894612168525087929 1332467920959126393815947)
                      ·
                        rfl

theorem cell23_2594972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_2594972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2594972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2594972 prefixEnd_2594972 := by exact prefixLift 2594972
  have htrace : WordTrace (prefixWord ++ tailWord_2594972) baseStart_2594972 baseEnd_2594972 := by
    simpa [prefixWord, tailWord_2594972, baseEnd_2594972] using wordTrace_append hprefix tailTrace_2594972
  have hstable : (prefixWord ++ tailWord_2594972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594972).length < 2 ^ (prefixWord ++ tailWord_2594972).sum := by decide
  have hdescent : baseEnd_2594972 < baseStart_2594972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594989 : List Nat := [1, 5, 2, 1, 2, 1, 1, 2, 2, 4, 2]
def baseStart_2594989 : Nat := 118140960795 + 2594989 * 2 ^ 59
def prefixEnd_2594989 : Nat := 4983230072969 + 3 ^ 40 * 2594989 * 2
def baseEnd_2594989 : Nat := 1332476650130252827303369

theorem tailTrace_2594989 : CollatzResearch.WordTrace tailWord_2594989 prefixEnd_2594989 1332476650130252827303369 := by
  unfold tailWord_2594989
  simp only [CollatzResearch.WordTrace]
  refine ⟨94647024395805516682244021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63098016263870344454829347 94647024395805516682244021)
  ·
    refine ⟨8873158537106767188960377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 94647024395805516682244021 8873158537106767188960377)
    ·
      refine ⟨6654868902830075391720283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8873158537106767188960377 6654868902830075391720283)
      ·
        refine ⟨9982303354245113087580425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6654868902830075391720283 9982303354245113087580425)
        ·
          refine ⟨7486727515683834815685319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9982303354245113087580425 7486727515683834815685319)
          ·
            refine ⟨11230091273525752223527979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7486727515683834815685319 11230091273525752223527979)
            ·
              refine ⟨16845136910288628335291969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11230091273525752223527979 16845136910288628335291969)
              ·
                refine ⟨12633852682716471251468977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16845136910288628335291969 12633852682716471251468977)
                ·
                  refine ⟨9475389512037353438601733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12633852682716471251468977 9475389512037353438601733)
                  ·
                    refine ⟨1776635533507003769737825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9475389512037353438601733 1776635533507003769737825)
                    ·
                      refine ⟨1332476650130252827303369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1776635533507003769737825 1332476650130252827303369)
                      ·
                        rfl

theorem cell23_2594989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_2594989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2594989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2594989 prefixEnd_2594989 := by exact prefixLift 2594989
  have htrace : WordTrace (prefixWord ++ tailWord_2594989) baseStart_2594989 baseEnd_2594989 := by
    simpa [prefixWord, tailWord_2594989, baseEnd_2594989] using wordTrace_append hprefix tailTrace_2594989
  have hstable : (prefixWord ++ tailWord_2594989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594989).length < 2 ^ (prefixWord ++ tailWord_2594989).sum := by decide
  have hdescent : baseEnd_2594989 < baseStart_2594989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594999 : List Nat := [1, 1, 3, 1, 4, 2, 2, 4, 1, 4]
def baseStart_2594999 : Nat := 118140960795 + 2594999 * 2 ^ 59
def prefixEnd_2594999 : Nat := 4983230072969 + 3 ^ 40 * 2594999 * 2
def baseEnd_2594999 : Nat := 444160594978932596059441

theorem tailTrace_2594999 : CollatzResearch.WordTrace tailWord_2594999 prefixEnd_2594999 444160594978932596059441 := by
  unfold tailWord_2594999
  simp only [CollatzResearch.WordTrace]
  refine ⟨94647389125769288390108051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63098259417179525593405367 94647389125769288390108051)
  ·
    refine ⟨141971083688653932585162077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94647389125769288390108051 141971083688653932585162077)
    ·
      refine ⟨53239156383245224719435779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141971083688653932585162077 53239156383245224719435779)
      ·
        refine ⟨79858734574867837079153669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53239156383245224719435779 79858734574867837079153669)
        ·
          refine ⟨14973512732787719452341313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79858734574867837079153669 14973512732787719452341313)
          ·
            refine ⟨11230134549590789589255985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14973512732787719452341313 11230134549590789589255985)
            ·
              refine ⟨8422600912193092191941989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11230134549590789589255985 8422600912193092191941989)
              ·
                refine ⟨1579237671036204785989123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8422600912193092191941989 1579237671036204785989123)
                ·
                  refine ⟨2368856506554307178983685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1579237671036204785989123 2368856506554307178983685)
                  ·
                    refine ⟨444160594978932596059441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2368856506554307178983685 444160594978932596059441)
                    ·
                      rfl

theorem cell23_2594999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 4, 1, 4].length) (baseStart_2594999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2594999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2594999 prefixEnd_2594999 := by exact prefixLift 2594999
  have htrace : WordTrace (prefixWord ++ tailWord_2594999) baseStart_2594999 baseEnd_2594999 := by
    simpa [prefixWord, tailWord_2594999, baseEnd_2594999] using wordTrace_append hprefix tailTrace_2594999
  have hstable : (prefixWord ++ tailWord_2594999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594999).length < 2 ^ (prefixWord ++ tailWord_2594999).sum := by decide
  have hdescent : baseEnd_2594999 < baseStart_2594999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595025 : List Nat := [1, 2, 2, 1, 2, 2, 2, 3, 3, 5]
def baseStart_2595025 : Nat := 118140960795 + 2595025 * 2 ^ 59
def prefixEnd_2595025 : Nat := 4983230072969 + 3 ^ 40 * 2595025 * 2
def baseEnd_2595025 : Nat := 444165045144604895484401

theorem tailTrace_2595025 : CollatzResearch.WordTrace tailWord_2595025 prefixEnd_2595025 444165045144604895484401 := by
  unfold tailWord_2595025
  simp only [CollatzResearch.WordTrace]
  refine ⟨94648337423675094830554529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63098891615783396553703019 94648337423675094830554529)
  ·
    refine ⟨70986253067756321122915897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94648337423675094830554529 70986253067756321122915897)
    ·
      refine ⟨53239689800817240842186923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70986253067756321122915897 53239689800817240842186923)
      ·
        refine ⟨79859534701225861263280385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53239689800817240842186923 79859534701225861263280385)
        ·
          refine ⟨59894651025919395947460289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79859534701225861263280385 59894651025919395947460289)
          ·
            refine ⟨44920988269439546960595217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59894651025919395947460289 44920988269439546960595217)
            ·
              refine ⟨33690741202079660220446413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44920988269439546960595217 33690741202079660220446413)
              ·
                refine ⟨12634027950779872582667405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33690741202079660220446413 12634027950779872582667405)
                ·
                  refine ⟨4737760481542452218500277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12634027950779872582667405 4737760481542452218500277)
                  ·
                    refine ⟨444165045144604895484401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4737760481542452218500277 444165045144604895484401)
                    ·
                      rfl

theorem cell23_2595025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 3, 5].length) (baseStart_2595025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2595025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2595025 prefixEnd_2595025 := by exact prefixLift 2595025
  have htrace : WordTrace (prefixWord ++ tailWord_2595025) baseStart_2595025 baseEnd_2595025 := by
    simpa [prefixWord, tailWord_2595025, baseEnd_2595025] using wordTrace_append hprefix tailTrace_2595025
  have hstable : (prefixWord ++ tailWord_2595025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595025).length < 2 ^ (prefixWord ++ tailWord_2595025).sum := by decide
  have hdescent : baseEnd_2595025 < baseStart_2595025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595065 : List Nat := [1, 2, 1, 3, 1, 1, 2, 3, 3, 1, 5]
def baseStart_2595065 : Nat := 118140960795 + 2595065 * 2 ^ 59
def prefixEnd_2595065 : Nat := 4983230072969 + 3 ^ 40 * 2595065 * 2
def baseEnd_2595065 : Nat := 1332515674659994529953019

theorem tailTrace_2595065 : CollatzResearch.WordTrace tailWord_2595065 prefixEnd_2595065 1332515674659994529953019 := by
  unfold tailWord_2595065
  simp only [CollatzResearch.WordTrace]
  refine ⟨94649796343530181662010649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63099864229020121108007099 94649796343530181662010649)
  ·
    refine ⟨70987347257647636246507987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94649796343530181662010649 70987347257647636246507987)
    ·
      refine ⟨106481020886471454369761981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70987347257647636246507987 106481020886471454369761981)
      ·
        refine ⟨39930382832426795388660743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106481020886471454369761981 39930382832426795388660743)
        ·
          refine ⟨59895574248640193082991115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39930382832426795388660743 59895574248640193082991115)
          ·
            refine ⟨89843361372960289624486673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59895574248640193082991115 89843361372960289624486673)
            ·
              refine ⟨67382521029720217218365005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89843361372960289624486673 67382521029720217218365005)
              ·
                refine ⟨25268445386145081456886877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67382521029720217218365005 25268445386145081456886877)
                ·
                  refine ⟨9475667019804405546332579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25268445386145081456886877 9475667019804405546332579)
                  ·
                    refine ⟨14213500529706608319498869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9475667019804405546332579 14213500529706608319498869)
                    ·
                      refine ⟨1332515674659994529953019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14213500529706608319498869 1332515674659994529953019)
                      ·
                        rfl

theorem cell23_2595065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_2595065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2595065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2595065 prefixEnd_2595065 := by exact prefixLift 2595065
  have htrace : WordTrace (prefixWord ++ tailWord_2595065) baseStart_2595065 baseEnd_2595065 := by
    simpa [prefixWord, tailWord_2595065, baseEnd_2595065] using wordTrace_append hprefix tailTrace_2595065
  have hstable : (prefixWord ++ tailWord_2595065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595065).length < 2 ^ (prefixWord ++ tailWord_2595065).sum := by decide
  have hdescent : baseEnd_2595065 < baseStart_2595065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595075 : List Nat := [1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 6]
def baseStart_2595075 : Nat := 118140960795 + 2595075 * 2 ^ 59
def prefixEnd_2595075 : Nat := 4983230072969 + 3 ^ 40 * 2595075 * 2
def baseEnd_2595075 : Nat := 1332520809466539490827973

theorem tailTrace_2595075 : CollatzResearch.WordTrace tailWord_2595075 prefixEnd_2595075 1332520809466539490827973 := by
  unfold tailWord_2595075
  simp only [CollatzResearch.WordTrace]
  refine ⟨94650161073493953369874679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63100107382329302246583119 94650161073493953369874679)
  ·
    refine ⟨141975241610240930054812019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94650161073493953369874679 141975241610240930054812019)
    ·
      refine ⟨212962862415361395082218029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141975241610240930054812019 212962862415361395082218029)
      ·
        refine ⟨79861073405760523155831761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 212962862415361395082218029 79861073405760523155831761)
        ·
          refine ⟨59895805054320392366873821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79861073405760523155831761 59895805054320392366873821)
          ·
            refine ⟨22460926895370147137577683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59895805054320392366873821 22460926895370147137577683)
            ·
              refine ⟨33691390343055220706366525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22460926895370147137577683 33691390343055220706366525)
              ·
                refine ⟨12634271378645707764887447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33691390343055220706366525 12634271378645707764887447)
                ·
                  refine ⟨18951407067968561647331171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12634271378645707764887447 18951407067968561647331171)
                  ·
                    refine ⟨28427110601952842470996757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18951407067968561647331171 28427110601952842470996757)
                    ·
                      refine ⟨1332520809466539490827973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28427110601952842470996757 1332520809466539490827973)
                      ·
                        rfl

theorem cell23_2595075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 6].length) (baseStart_2595075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2595075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2595075 prefixEnd_2595075 := by exact prefixLift 2595075
  have htrace : WordTrace (prefixWord ++ tailWord_2595075) baseStart_2595075 baseEnd_2595075 := by
    simpa [prefixWord, tailWord_2595075, baseEnd_2595075] using wordTrace_append hprefix tailTrace_2595075
  have hstable : (prefixWord ++ tailWord_2595075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595075).length < 2 ^ (prefixWord ++ tailWord_2595075).sum := by decide
  have hdescent : baseEnd_2595075 < baseStart_2595075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
