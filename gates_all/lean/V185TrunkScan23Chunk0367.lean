import V185TrunkScan23Chunk0366

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2170175 : List Nat := [1, 1, 2, 2, 4, 2, 1, 4, 1, 3, 2]
def baseStart_2170175 : Nat := 118140960795 + 2170175 * 2 ^ 59
def prefixEnd_2170175 : Nat := 4983230072969 + 3 ^ 40 * 2170175 * 2
def baseEnd_2170175 : Nat := 1114342879371151914032053

theorem tailTrace_2170175 : CollatzResearch.WordTrace tailWord_2170175 prefixEnd_2170175 1114342879371151914032053 := by
  unfold tailWord_2170175
  simp only [CollatzResearch.WordTrace]
  refine ⟨79152784912834086227239979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52768523275222724151493319 79152784912834086227239979)
  ·
    refine ⟨118729177369251129340859969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79152784912834086227239979 118729177369251129340859969)
    ·
      refine ⟨89046883026938347005644977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118729177369251129340859969 89046883026938347005644977)
      ·
        refine ⟨66785162270203760254233733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89046883026938347005644977 66785162270203760254233733)
        ·
          refine ⟨12522217925663205047668825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66785162270203760254233733 12522217925663205047668825)
          ·
            refine ⟨9391663444247403785751619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12522217925663205047668825 9391663444247403785751619)
            ·
              refine ⟨14087495166371105678627429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9391663444247403785751619 14087495166371105678627429)
              ·
                refine ⟨2641405343694582314742643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14087495166371105678627429 2641405343694582314742643)
                ·
                  refine ⟨3962108015541873472113965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2641405343694582314742643 3962108015541873472113965)
                  ·
                    refine ⟨1485790505828202552042737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3962108015541873472113965 1485790505828202552042737)
                    ·
                      refine ⟨1114342879371151914032053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1485790505828202552042737 1114342879371151914032053)
                      ·
                        rfl

theorem cell23_2170175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 4, 1, 3, 2].length) (baseStart_2170175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2170175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2170175 prefixEnd_2170175 := by exact prefixLift 2170175
  have htrace : WordTrace (prefixWord ++ tailWord_2170175) baseStart_2170175 baseEnd_2170175 := by
    simpa [prefixWord, tailWord_2170175, baseEnd_2170175] using wordTrace_append hprefix tailTrace_2170175
  have hstable : (prefixWord ++ tailWord_2170175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170175).length < 2 ^ (prefixWord ++ tailWord_2170175).sum := by decide
  have hdescent : baseEnd_2170175 < baseStart_2170175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170201 : List Nat := [1, 2, 1, 2, 2, 2, 2, 1, 4, 2, 4]
def baseStart_2170201 : Nat := 118140960795 + 2170201 * 2 ^ 59
def prefixEnd_2170201 : Nat := 4983230072969 + 3 ^ 40 * 2170201 * 2
def baseEnd_2170201 : Nat := 1114356229868168812306933

theorem tailTrace_2170201 : CollatzResearch.WordTrace tailWord_2170201 prefixEnd_2170201 1114356229868168812306933 := by
  unfold tailWord_2170201
  simp only [CollatzResearch.WordTrace]
  refine ⟨79153733210739892667686457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52769155473826595111790971 79153733210739892667686457)
  ·
    refine ⟨59365299908054919500764843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79153733210739892667686457 59365299908054919500764843)
    ·
      refine ⟨89047949862082379251147265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59365299908054919500764843 89047949862082379251147265)
      ·
        refine ⟨66785962396561784438360449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89047949862082379251147265 66785962396561784438360449)
        ·
          refine ⟨50089471797421338328770337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66785962396561784438360449 50089471797421338328770337)
          ·
            refine ⟨37567103848066003746577753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50089471797421338328770337 37567103848066003746577753)
            ·
              refine ⟨28175327886049502809933315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37567103848066003746577753 28175327886049502809933315)
              ·
                refine ⟨42262991829074254214899973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28175327886049502809933315 42262991829074254214899973)
                ·
                  refine ⟨7924310967951422665293745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42262991829074254214899973 7924310967951422665293745)
                  ·
                    refine ⟨5943233225963566998970309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7924310967951422665293745 5943233225963566998970309)
                    ·
                      refine ⟨1114356229868168812306933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5943233225963566998970309 1114356229868168812306933)
                      ·
                        rfl

theorem cell23_2170201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4, 2, 4].length) (baseStart_2170201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2170201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2170201 prefixEnd_2170201 := by exact prefixLift 2170201
  have htrace : WordTrace (prefixWord ++ tailWord_2170201) baseStart_2170201 baseEnd_2170201 := by
    simpa [prefixWord, tailWord_2170201, baseEnd_2170201] using wordTrace_append hprefix tailTrace_2170201
  have hstable : (prefixWord ++ tailWord_2170201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170201).length < 2 ^ (prefixWord ++ tailWord_2170201).sum := by decide
  have hdescent : baseEnd_2170201 < baseStart_2170201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170216 : List Nat := [2, 1, 4, 2, 4, 1, 2, 1, 2, 1, 3]
def baseStart_2170216 : Nat := 118140960795 + 2170216 * 2 ^ 59
def prefixEnd_2170216 : Nat := 4983230072969 + 3 ^ 40 * 2170216 * 2
def baseEnd_2170216 : Nat := 1114363932077986253619365

theorem tailTrace_2170216 : CollatzResearch.WordTrace tailWord_2170216 prefixEnd_2170216 1114363932077986253619365 := by
  unfold tailWord_2170216
  simp only [CollatzResearch.WordTrace]
  refine ⟨39577140152842775114741251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52769520203790366819655001 39577140152842775114741251)
  ·
    refine ⟨59365710229264162672111877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39577140152842775114741251 59365710229264162672111877)
    ·
      refine ⟨11131070667987030501020977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59365710229264162672111877 11131070667987030501020977)
      ·
        refine ⟨8348303000990272875765733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11131070667987030501020977 8348303000990272875765733)
        ·
          refine ⟨1565306812685676164206075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8348303000990272875765733 1565306812685676164206075)
          ·
            refine ⟨2347960219028514246309113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1565306812685676164206075 2347960219028514246309113)
            ·
              refine ⟨1760970164271385684731835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2347960219028514246309113 1760970164271385684731835)
              ·
                refine ⟨2641455246407078527097753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1760970164271385684731835 2641455246407078527097753)
                ·
                  refine ⟨1981091434805308895323315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2641455246407078527097753 1981091434805308895323315)
                  ·
                    refine ⟨2971637152207963342984973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1981091434805308895323315 2971637152207963342984973)
                    ·
                      refine ⟨1114363932077986253619365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2971637152207963342984973 1114363932077986253619365)
                      ·
                        rfl

theorem cell23_2170216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_2170216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2170216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2170216 prefixEnd_2170216 := by exact prefixLift 2170216
  have htrace : WordTrace (prefixWord ++ tailWord_2170216) baseStart_2170216 baseEnd_2170216 := by
    simpa [prefixWord, tailWord_2170216, baseEnd_2170216] using wordTrace_append hprefix tailTrace_2170216
  have hstable : (prefixWord ++ tailWord_2170216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170216).length < 2 ^ (prefixWord ++ tailWord_2170216).sum := by decide
  have hdescent : baseEnd_2170216 < baseStart_2170216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170251 : List Nat := [1, 1, 1, 1, 4, 3, 1, 1, 3, 2, 5]
def baseStart_2170251 : Nat := 118140960795 + 2170251 * 2 ^ 59
def prefixEnd_2170251 : Nat := 4983230072969 + 3 ^ 40 * 2170251 * 2
def baseEnd_2170251 : Nat := 1114381903900893616681703

theorem tailTrace_2170251 : CollatzResearch.WordTrace tailWord_2170251 prefixEnd_2170251 1114381903900893616681703 := by
  unfold tailWord_2170251
  simp only [CollatzResearch.WordTrace]
  refine ⟨79155556860558751207006607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52770371240372500804671071 79155556860558751207006607)
  ·
    refine ⟨118733335290838126810509911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79155556860558751207006607 118733335290838126810509911)
    ·
      refine ⟨178100002936257190215764867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118733335290838126810509911 178100002936257190215764867)
      ·
        refine ⟨267150004404385785323647301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178100002936257190215764867 267150004404385785323647301)
        ·
          refine ⟨50090625825822334748183869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 267150004404385785323647301 50090625825822334748183869)
          ·
            refine ⟨18783984684683375530568951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50090625825822334748183869 18783984684683375530568951)
            ·
              refine ⟨28175977027025063295853427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18783984684683375530568951 28175977027025063295853427)
              ·
                refine ⟨42263965540537594943780141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28175977027025063295853427 42263965540537594943780141)
                ·
                  refine ⟨15848987077701598103917553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42263965540537594943780141 15848987077701598103917553)
                  ·
                    refine ⟨11886740308276198577938165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15848987077701598103917553 11886740308276198577938165)
                    ·
                      refine ⟨1114381903900893616681703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11886740308276198577938165 1114381903900893616681703)
                      ·
                        rfl

theorem cell23_2170251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2, 5].length) (baseStart_2170251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2170251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2170251 prefixEnd_2170251 := by exact prefixLift 2170251
  have htrace : WordTrace (prefixWord ++ tailWord_2170251) baseStart_2170251 baseEnd_2170251 := by
    simpa [prefixWord, tailWord_2170251, baseEnd_2170251] using wordTrace_append hprefix tailTrace_2170251
  have hstable : (prefixWord ++ tailWord_2170251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170251).length < 2 ^ (prefixWord ++ tailWord_2170251).sum := by decide
  have hdescent : baseEnd_2170251 < baseStart_2170251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170291 : List Nat := [1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 6]
def baseStart_2170291 : Nat := 118140960795 + 2170291 * 2 ^ 59
def prefixEnd_2170291 : Nat := 4983230072969 + 3 ^ 40 * 2170291 * 2
def baseEnd_2170291 : Nat := 1114402443127073460181519

theorem tailTrace_2170291 : CollatzResearch.WordTrace tailWord_2170291 prefixEnd_2170291 1114402443127073460181519 := by
  unfold tailWord_2170291
  simp only [CollatzResearch.WordTrace]
  refine ⟨79157015780413838038462727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52771343853609225358975151 79157015780413838038462727)
  ·
    refine ⟨118735523670620757057694091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79157015780413838038462727 118735523670620757057694091)
    ·
      refine ⟨178103285505931135586541137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118735523670620757057694091 178103285505931135586541137)
      ·
        refine ⟨133577464129448351689905853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178103285505931135586541137 133577464129448351689905853)
        ·
          refine ⟨50091549048543131883714695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133577464129448351689905853 50091549048543131883714695)
          ·
            refine ⟨75137323572814697825572043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50091549048543131883714695 75137323572814697825572043)
            ·
              refine ⟨112705985359222046738358065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75137323572814697825572043 112705985359222046738358065)
              ·
                refine ⟨84529489019416535053768549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112705985359222046738358065 84529489019416535053768549)
                ·
                  refine ⟨15849279191140600322581603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 84529489019416535053768549 15849279191140600322581603)
                  ·
                    refine ⟨23773918786710900483872405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15849279191140600322581603 23773918786710900483872405)
                    ·
                      refine ⟨1114402443127073460181519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23773918786710900483872405 1114402443127073460181519)
                      ·
                        rfl

theorem cell23_2170291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 6].length) (baseStart_2170291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2170291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2170291 prefixEnd_2170291 := by exact prefixLift 2170291
  have htrace : WordTrace (prefixWord ++ tailWord_2170291) baseStart_2170291 baseEnd_2170291 := by
    simpa [prefixWord, tailWord_2170291, baseEnd_2170291] using wordTrace_append hprefix tailTrace_2170291
  have hstable : (prefixWord ++ tailWord_2170291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170291).length < 2 ^ (prefixWord ++ tailWord_2170291).sum := by decide
  have hdescent : baseEnd_2170291 < baseStart_2170291 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170335 : List Nat := [1, 1, 2, 3, 3, 1, 5, 1, 6]
def baseStart_2170335 : Nat := 118140960795 + 2170335 * 2 ^ 59
def prefixEnd_2170335 : Nat := 4983230072969 + 3 ^ 40 * 2170335 * 2
def baseEnd_2170335 : Nat := 123825004030652365336813

theorem tailTrace_2170335 : CollatzResearch.WordTrace tailWord_2170335 prefixEnd_2170335 123825004030652365336813 := by
  unfold tailWord_2170335
  simp only [CollatzResearch.WordTrace]
  refine ⟨79158620592254433553064459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52772413728169622368709639 79158620592254433553064459)
  ·
    refine ⟨118737930888381650329596689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79158620592254433553064459 118737930888381650329596689)
    ·
      refine ⟨89053448166286237747197517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118737930888381650329596689 89053448166286237747197517)
      ·
        refine ⟨33395043062357339155199069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89053448166286237747197517 33395043062357339155199069)
        ·
          refine ⟨12523141148384002183199651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33395043062357339155199069 12523141148384002183199651)
          ·
            refine ⟨18784711722576003274799477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12523141148384002183199651 18784711722576003274799477)
            ·
              refine ⟨1761066723991500307012451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18784711722576003274799477 1761066723991500307012451)
              ·
                refine ⟨2641600085987250460518677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1761066723991500307012451 2641600085987250460518677)
                ·
                  refine ⟨123825004030652365336813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2641600085987250460518677 123825004030652365336813)
                  ·
                    rfl

theorem cell23_2170335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 1, 6].length) (baseStart_2170335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2170335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2170335 prefixEnd_2170335 := by exact prefixLift 2170335
  have htrace : WordTrace (prefixWord ++ tailWord_2170335) baseStart_2170335 baseEnd_2170335 := by
    simpa [prefixWord, tailWord_2170335, baseEnd_2170335] using wordTrace_append hprefix tailTrace_2170335
  have hstable : (prefixWord ++ tailWord_2170335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170335).length < 2 ^ (prefixWord ++ tailWord_2170335).sum := by decide
  have hdescent : baseEnd_2170335 < baseStart_2170335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170365 : List Nat := [1, 4, 1, 1, 1, 4, 2, 3, 1, 5]
def baseStart_2170365 : Nat := 118140960795 + 2170365 * 2 ^ 59
def prefixEnd_2170365 : Nat := 4983230072969 + 3 ^ 40 * 2170365 * 2
def baseEnd_2170365 : Nat := 371480146898502056885393

theorem tailTrace_2170365 : CollatzResearch.WordTrace tailWord_2170365 prefixEnd_2170365 371480146898502056885393 := by
  unfold tailWord_2170365
  simp only [CollatzResearch.WordTrace]
  refine ⟨79159714782145748676656549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52773143188097165784437699 79159714782145748676656549)
  ·
    refine ⟨14842446521652327876873103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79159714782145748676656549 14842446521652327876873103)
    ·
      refine ⟨22263669782478491815309655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14842446521652327876873103 22263669782478491815309655)
      ·
        refine ⟨33395504673717737722964483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22263669782478491815309655 33395504673717737722964483)
        ·
          refine ⟨50093257010576606584446725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33395504673717737722964483 50093257010576606584446725)
          ·
            refine ⟨9392485689483113734583761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50093257010576606584446725 9392485689483113734583761)
            ·
              refine ⟨7044364267112335300937821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9392485689483113734583761 7044364267112335300937821)
              ·
                refine ⟨2641636600167125737851683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7044364267112335300937821 2641636600167125737851683)
                ·
                  refine ⟨3962454900250688606777525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2641636600167125737851683 3962454900250688606777525)
                  ·
                    refine ⟨371480146898502056885393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3962454900250688606777525 371480146898502056885393)
                    ·
                      rfl

theorem cell23_2170365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 3, 1, 5].length) (baseStart_2170365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2170365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2170365 prefixEnd_2170365 := by exact prefixLift 2170365
  have htrace : WordTrace (prefixWord ++ tailWord_2170365) baseStart_2170365 baseEnd_2170365 := by
    simpa [prefixWord, tailWord_2170365, baseEnd_2170365] using wordTrace_append hprefix tailTrace_2170365
  have hstable : (prefixWord ++ tailWord_2170365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170365).length < 2 ^ (prefixWord ++ tailWord_2170365).sum := by decide
  have hdescent : baseEnd_2170365 < baseStart_2170365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170379 : List Nat := [1, 1, 1, 1, 8, 2, 1, 1, 3, 1, 3]
def baseStart_2170379 : Nat := 118140960795 + 2170379 * 2 ^ 59
def prefixEnd_2170379 : Nat := 4983230072969 + 3 ^ 40 * 2170379 * 2
def baseEnd_2170379 : Nat := 1114447629424669115881115

theorem tailTrace_2170379 : CollatzResearch.WordTrace tailWord_2170379 prefixEnd_2170379 1114447629424669115881115 := by
  unfold tailWord_2170379
  simp only [CollatzResearch.WordTrace]
  refine ⟨79160225404095029067666191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52773483602730019378444127 79160225404095029067666191)
  ·
    refine ⟨118740338106142543601499287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79160225404095029067666191 118740338106142543601499287)
    ·
      refine ⟨178110507159213815402248931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118740338106142543601499287 178110507159213815402248931)
      ·
        refine ⟨267165760738820723103373397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178110507159213815402248931 267165760738820723103373397)
        ·
          refine ⟨3130848758658055348867657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 267165760738820723103373397 3130848758658055348867657)
          ·
            refine ⟨2348136568993541511650743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3130848758658055348867657 2348136568993541511650743)
            ·
              refine ⟨3522204853490312267476115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2348136568993541511650743 3522204853490312267476115)
              ·
                refine ⟨5283307280235468401214173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3522204853490312267476115 5283307280235468401214173)
                ·
                  refine ⟨1981240230088300650455315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5283307280235468401214173 1981240230088300650455315)
                  ·
                    refine ⟨2971860345132450975682973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1981240230088300650455315 2971860345132450975682973)
                    ·
                      refine ⟨1114447629424669115881115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2971860345132450975682973 1114447629424669115881115)
                      ·
                        rfl

theorem cell23_2170379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 1, 3, 1, 3].length) (baseStart_2170379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2170379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2170379 prefixEnd_2170379 := by exact prefixLift 2170379
  have htrace : WordTrace (prefixWord ++ tailWord_2170379) baseStart_2170379 baseEnd_2170379 := by
    simpa [prefixWord, tailWord_2170379, baseEnd_2170379] using wordTrace_append hprefix tailTrace_2170379
  have hstable : (prefixWord ++ tailWord_2170379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170379).length < 2 ^ (prefixWord ++ tailWord_2170379).sum := by decide
  have hdescent : baseEnd_2170379 < baseStart_2170379 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170402 : List Nat := [3, 3, 1, 1, 1, 1, 5, 2, 1, 1, 4]
def baseStart_2170402 : Nat := 118140960795 + 2170402 * 2 ^ 59
def prefixEnd_2170402 : Nat := 4983230072969 + 3 ^ 40 * 2170402 * 2
def baseEnd_2170402 : Nat := 1114459439479722525893509

theorem tailTrace_2170402 : CollatzResearch.WordTrace tailWord_2170402 prefixEnd_2170402 1114459439479722525893509 := by
  unfold tailWord_2170402
  simp only [CollatzResearch.WordTrace]
  refine ⟨19790266070752925998938365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52774042855341135997168973 19790266070752925998938365)
  ·
    refine ⟨7421349776532347249601887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19790266070752925998938365 7421349776532347249601887)
    ·
      refine ⟨11132024664798520874402831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7421349776532347249601887 11132024664798520874402831)
      ·
        refine ⟨16698036997197781311604247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11132024664798520874402831 16698036997197781311604247)
        ·
          refine ⟨25047055495796671967406371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16698036997197781311604247 25047055495796671967406371)
          ·
            refine ⟨37570583243695007951109557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25047055495796671967406371 37570583243695007951109557)
            ·
              refine ⟨3522242179096406995416521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37570583243695007951109557 3522242179096406995416521)
              ·
                refine ⟨2641681634322305246562391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3522242179096406995416521 2641681634322305246562391)
                ·
                  refine ⟨3962522451483457869843587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2641681634322305246562391 3962522451483457869843587)
                  ·
                    refine ⟨5943783677225186804765381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3962522451483457869843587 5943783677225186804765381)
                    ·
                      refine ⟨1114459439479722525893509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5943783677225186804765381 1114459439479722525893509)
                      ·
                        rfl

theorem cell23_2170402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_2170402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2170402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2170402 prefixEnd_2170402 := by exact prefixLift 2170402
  have htrace : WordTrace (prefixWord ++ tailWord_2170402) baseStart_2170402 baseEnd_2170402 := by
    simpa [prefixWord, tailWord_2170402, baseEnd_2170402] using wordTrace_append hprefix tailTrace_2170402
  have hstable : (prefixWord ++ tailWord_2170402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170402).length < 2 ^ (prefixWord ++ tailWord_2170402).sum := by decide
  have hdescent : baseEnd_2170402 < baseStart_2170402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170429 : List Nat := [1, 4, 1, 3, 3, 1, 2, 2, 2, 4]
def baseStart_2170429 : Nat := 118140960795 + 2170429 * 2 ^ 59
def prefixEnd_2170429 : Nat := 4983230072969 + 3 ^ 40 * 2170429 * 2
def baseEnd_2170429 : Nat := 371491101152464640085295

theorem tailTrace_2170429 : CollatzResearch.WordTrace tailWord_2170429 prefixEnd_2170429 371491101152464640085295 := by
  unfold tailWord_2170429
  simp only [CollatzResearch.WordTrace]
  refine ⟨79162049053913887606986341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52774699369275925071324227 79162049053913887606986341)
  ·
    refine ⟨14842884197608853926309939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79162049053913887606986341 14842884197608853926309939)
    ·
      refine ⟨22264326296413280889464909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14842884197608853926309939 22264326296413280889464909)
      ·
        refine ⟨8349122361154980333549341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22264326296413280889464909 8349122361154980333549341)
        ·
          refine ⟨3130920885433117625081003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8349122361154980333549341 3130920885433117625081003)
          ·
            refine ⟨4696381328149676437621505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3130920885433117625081003 4696381328149676437621505)
            ·
              refine ⟨3522285996112257328216129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4696381328149676437621505 3522285996112257328216129)
              ·
                refine ⟨2641714497084192996162097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3522285996112257328216129 2641714497084192996162097)
                ·
                  refine ⟨1981285872813144747121573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2641714497084192996162097 1981285872813144747121573)
                  ·
                    refine ⟨371491101152464640085295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1981285872813144747121573 371491101152464640085295)
                    ·
                      rfl

theorem cell23_2170429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 2, 2, 4].length) (baseStart_2170429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2170429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2170429 prefixEnd_2170429 := by exact prefixLift 2170429
  have htrace : WordTrace (prefixWord ++ tailWord_2170429) baseStart_2170429 baseEnd_2170429 := by
    simpa [prefixWord, tailWord_2170429, baseEnd_2170429] using wordTrace_append hprefix tailTrace_2170429
  have hstable : (prefixWord ++ tailWord_2170429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170429).length < 2 ^ (prefixWord ++ tailWord_2170429).sum := by decide
  have hdescent : baseEnd_2170429 < baseStart_2170429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170452 : List Nat := [2, 4, 1, 1, 1, 2, 4, 1, 1, 3, 3]
def baseStart_2170452 : Nat := 118140960795 + 2170452 * 2 ^ 59
def prefixEnd_2170452 : Nat := 4983230072969 + 3 ^ 40 * 2170452 * 2
def baseEnd_2170452 : Nat := 1114485113512447330268279

theorem tailTrace_2170452 : CollatzResearch.WordTrace tailWord_2170452 prefixEnd_2170452 1114485113512447330268279 := by
  unfold tailWord_2170452
  simp only [CollatzResearch.WordTrace]
  refine ⟨39581443966415281267536805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52775258621887041690049073 39581443966415281267536805)
  ·
    refine ⟨7421520743702865237663151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39581443966415281267536805 7421520743702865237663151)
    ·
      refine ⟨11132281115554297856494727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7421520743702865237663151 11132281115554297856494727)
      ·
        refine ⟨16698421673331446784742091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11132281115554297856494727 16698421673331446784742091)
        ·
          refine ⟨25047632509997170177113137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16698421673331446784742091 25047632509997170177113137)
          ·
            refine ⟨18785724382497877632834853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25047632509997170177113137 18785724382497877632834853)
            ·
              refine ⟨3522323321718352056156535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18785724382497877632834853 3522323321718352056156535)
              ·
                refine ⟨5283484982577528084234803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3522323321718352056156535 5283484982577528084234803)
                ·
                  refine ⟨7925227473866292126352205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5283484982577528084234803 7925227473866292126352205)
                  ·
                    refine ⟨2971960302699859547382077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7925227473866292126352205 2971960302699859547382077)
                    ·
                      refine ⟨1114485113512447330268279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2971960302699859547382077 1114485113512447330268279)
                      ·
                        rfl

theorem cell23_2170452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_2170452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2170452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2170452 prefixEnd_2170452 := by exact prefixLift 2170452
  have htrace : WordTrace (prefixWord ++ tailWord_2170452) baseStart_2170452 baseEnd_2170452 := by
    simpa [prefixWord, tailWord_2170452, baseEnd_2170452] using wordTrace_append hprefix tailTrace_2170452
  have hstable : (prefixWord ++ tailWord_2170452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170452).length < 2 ^ (prefixWord ++ tailWord_2170452).sum := by decide
  have hdescent : baseEnd_2170452 < baseStart_2170452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170475 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 2, 8, 2]
def baseStart_2170475 : Nat := 118140960795 + 2170475 * 2 ^ 59
def prefixEnd_2170475 : Nat := 4983230072969 + 3 ^ 40 * 2170475 * 2
def baseEnd_2170475 : Nat := 1114496923567500740280673

theorem tailTrace_2170475 : CollatzResearch.WordTrace tailWord_2170475 prefixEnd_2170475 1114496923567500740280673 := by
  unfold tailWord_2170475
  simp only [CollatzResearch.WordTrace]
  refine ⟨79163726811747237463160879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52775817874498158308773919 79163726811747237463160879)
  ·
    refine ⟨118745590217620856194741319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79163726811747237463160879 118745590217620856194741319)
    ·
      refine ⟨178118385326431284292111979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118745590217620856194741319 178118385326431284292111979)
      ·
        refine ⟨267177577989646926438167969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178118385326431284292111979 267177577989646926438167969)
        ·
          refine ⟨200383183492235194828625977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 267177577989646926438167969 200383183492235194828625977)
          ·
            refine ⟨150287387619176396121469483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200383183492235194828625977 150287387619176396121469483)
            ·
              refine ⟨225431081428764594182204225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150287387619176396121469483 225431081428764594182204225)
              ·
                refine ⟨169073311071573445636653169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 225431081428764594182204225 169073311071573445636653169)
                ·
                  refine ⟨126804983303680084227489877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 169073311071573445636653169 126804983303680084227489877)
                  ·
                    refine ⟨1485995898090000987040897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 126804983303680084227489877 1485995898090000987040897)
                    ·
                      refine ⟨1114496923567500740280673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1485995898090000987040897 1114496923567500740280673)
                      ·
                        rfl

theorem cell23_2170475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 8, 2].length) (baseStart_2170475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2170475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2170475 prefixEnd_2170475 := by exact prefixLift 2170475
  have htrace : WordTrace (prefixWord ++ tailWord_2170475) baseStart_2170475 baseEnd_2170475 := by
    simpa [prefixWord, tailWord_2170475, baseEnd_2170475] using wordTrace_append hprefix tailTrace_2170475
  have hstable : (prefixWord ++ tailWord_2170475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170475).length < 2 ^ (prefixWord ++ tailWord_2170475).sum := by decide
  have hdescent : baseEnd_2170475 < baseStart_2170475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170486 : List Nat := [5, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3]
def baseStart_2170486 : Nat := 118140960795 + 2170486 * 2 ^ 59
def prefixEnd_2170486 : Nat := 4983230072969 + 3 ^ 40 * 2170486 * 2
def baseEnd_2170486 : Nat := 1114502571854700197243123

theorem tailTrace_2170486 : CollatzResearch.WordTrace tailWord_2170486 prefixEnd_2170486 1114502571854700197243123 := by
  unfold tailWord_2170486
  simp only [CollatzResearch.WordTrace]
  refine ⟨4947758000919211646363207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52776085343138257561207541 4947758000919211646363207)
  ·
    refine ⟨7421637001378817469544811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4947758000919211646363207 7421637001378817469544811)
    ·
      refine ⟨11132455502068226204317217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7421637001378817469544811 11132455502068226204317217)
      ·
        refine ⟨8349341626551169653237913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11132455502068226204317217 8349341626551169653237913)
        ·
          refine ⟨6262006219913377239928435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8349341626551169653237913 6262006219913377239928435)
          ·
            refine ⟨9393009329870065859892653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6262006219913377239928435 9393009329870065859892653)
            ·
              refine ⟨3522378498701274697459745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9393009329870065859892653 3522378498701274697459745)
              ·
                refine ⟨2641783874025956023094809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3522378498701274697459745 2641783874025956023094809)
                ·
                  refine ⟨1981337905519467017321107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2641783874025956023094809 1981337905519467017321107)
                  ·
                    refine ⟨2972006858279200525981661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1981337905519467017321107 2972006858279200525981661)
                    ·
                      refine ⟨1114502571854700197243123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2972006858279200525981661 1114502571854700197243123)
                      ·
                        rfl

theorem cell23_2170486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_2170486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2170486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2170486 prefixEnd_2170486 := by exact prefixLift 2170486
  have htrace : WordTrace (prefixWord ++ tailWord_2170486) baseStart_2170486 baseEnd_2170486 := by
    simpa [prefixWord, tailWord_2170486, baseEnd_2170486] using wordTrace_append hprefix tailTrace_2170486
  have hstable : (prefixWord ++ tailWord_2170486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170486).length < 2 ^ (prefixWord ++ tailWord_2170486).sum := by decide
  have hdescent : baseEnd_2170486 < baseStart_2170486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170488 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 1, 5, 6]
def baseStart_2170488 : Nat := 118140960795 + 2170488 * 2 ^ 59
def prefixEnd_2170488 : Nat := 4983230072969 + 3 ^ 40 * 2170488 * 2
def baseEnd_2170488 : Nat := 1114503598816009189418113

theorem tailTrace_2170488 : CollatzResearch.WordTrace tailWord_2170488 prefixEnd_2170488 1114503598816009189418113 := by
  unfold tailWord_2170488
  simp only [CollatzResearch.WordTrace]
  refine ⟨39582100480350070341692059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52776133973800093788922745 39582100480350070341692059)
  ·
    refine ⟨59373150720525105512538089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39582100480350070341692059 59373150720525105512538089)
    ·
      refine ⟨44529863040393829134403567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59373150720525105512538089 44529863040393829134403567)
      ·
        refine ⟨66794794560590743701605351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44529863040393829134403567 66794794560590743701605351)
        ·
          refine ⟨100192191840886115552408027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66794794560590743701605351 100192191840886115552408027)
          ·
            refine ⟨150288287761329173328612041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100192191840886115552408027 150288287761329173328612041)
            ·
              refine ⟨112716215820996879996459031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150288287761329173328612041 112716215820996879996459031)
              ·
                refine ⟨169074323731495319994688547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112716215820996879996459031 169074323731495319994688547)
                ·
                  refine ⟨253611485597242979992032821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 169074323731495319994688547 253611485597242979992032821)
                  ·
                    refine ⟨23776076774741529374253077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 253611485597242979992032821 23776076774741529374253077)
                    ·
                      refine ⟨1114503598816009189418113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23776076774741529374253077 1114503598816009189418113)
                      ·
                        rfl

theorem cell23_2170488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 5, 6].length) (baseStart_2170488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2170488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2170488 prefixEnd_2170488 := by exact prefixLift 2170488
  have htrace : WordTrace (prefixWord ++ tailWord_2170488) baseStart_2170488 baseEnd_2170488 := by
    simpa [prefixWord, tailWord_2170488, baseEnd_2170488] using wordTrace_append hprefix tailTrace_2170488
  have hstable : (prefixWord ++ tailWord_2170488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170488).length < 2 ^ (prefixWord ++ tailWord_2170488).sum := by decide
  have hdescent : baseEnd_2170488 < baseStart_2170488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170505 : List Nat := [1, 2, 1, 1, 4, 1, 4, 1, 2, 2, 4]
def baseStart_2170505 : Nat := 118140960795 + 2170505 * 2 ^ 59
def prefixEnd_2170505 : Nat := 4983230072969 + 3 ^ 40 * 2170505 * 2
def baseEnd_2170505 : Nat := 1114512327987135622905535

theorem tailTrace_2170505 : CollatzResearch.WordTrace tailWord_2170505 prefixEnd_2170505 1114512327987135622905535 := by
  unfold tailWord_2170505
  simp only [CollatzResearch.WordTrace]
  refine ⟨79164821001638552586752969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52776547334425701724501979 79164821001638552586752969)
  ·
    refine ⟨59373615751228914440064727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79164821001638552586752969 59373615751228914440064727)
    ·
      refine ⟨89060423626843371660097091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59373615751228914440064727 89060423626843371660097091)
      ·
        refine ⟨133590635440265057490145637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89060423626843371660097091 133590635440265057490145637)
        ·
          refine ⟨25048244145049698279402307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 133590635440265057490145637 25048244145049698279402307)
          ·
            refine ⟨37572366217574547419103461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25048244145049698279402307 37572366217574547419103461)
            ·
              refine ⟨7044818665795227641081899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37572366217574547419103461 7044818665795227641081899)
              ·
                refine ⟨10567227998692841461622849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7044818665795227641081899 10567227998692841461622849)
                ·
                  refine ⟨7925420999019631096217137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10567227998692841461622849 7925420999019631096217137)
                  ·
                    refine ⟨5944065749264723322162853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7925420999019631096217137 5944065749264723322162853)
                    ·
                      refine ⟨1114512327987135622905535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5944065749264723322162853 1114512327987135622905535)
                      ·
                        rfl

theorem cell23_2170505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 2, 2, 4].length) (baseStart_2170505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2170505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2170505 prefixEnd_2170505 := by exact prefixLift 2170505
  have htrace : WordTrace (prefixWord ++ tailWord_2170505) baseStart_2170505 baseEnd_2170505 := by
    simpa [prefixWord, tailWord_2170505, baseEnd_2170505] using wordTrace_append hprefix tailTrace_2170505
  have hstable : (prefixWord ++ tailWord_2170505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170505).length < 2 ^ (prefixWord ++ tailWord_2170505).sum := by decide
  have hdescent : baseEnd_2170505 < baseStart_2170505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170526 : List Nat := [4, 3, 1, 1, 1, 2, 1, 2, 4, 2, 2]
def baseStart_2170526 : Nat := 118140960795 + 2170526 * 2 ^ 59
def prefixEnd_2170526 : Nat := 4983230072969 + 3 ^ 40 * 2170526 * 2
def baseEnd_2170526 : Nat := 1114523111080880040742939

theorem tailTrace_2170526 : CollatzResearch.WordTrace tailWord_2170526 prefixEnd_2170526 1114523111080880040742939 := by
  unfold tailWord_2170526
  simp only [CollatzResearch.WordTrace]
  refine ⟨9895698366820309146658429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52777057956374982115511621 9895698366820309146658429)
  ·
    refine ⟨3710886887557615929996911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9895698366820309146658429 3710886887557615929996911)
    ·
      refine ⟨5566330331336423894995367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3710886887557615929996911 5566330331336423894995367)
      ·
        refine ⟨8349495497004635842493051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5566330331336423894995367 8349495497004635842493051)
        ·
          refine ⟨12524243245506953763739577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8349495497004635842493051 12524243245506953763739577)
          ·
            refine ⟨9393182434130215322804683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12524243245506953763739577 9393182434130215322804683)
            ·
              refine ⟨14089773651195322984207025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9393182434130215322804683 14089773651195322984207025)
              ·
                refine ⟨10567330238396492238155269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14089773651195322984207025 10567330238396492238155269)
                ·
                  refine ⟨1981374419699342294654113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10567330238396492238155269 1981374419699342294654113)
                  ·
                    refine ⟨1486030814774506720990585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1981374419699342294654113 1486030814774506720990585)
                    ·
                      refine ⟨1114523111080880040742939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1486030814774506720990585 1114523111080880040742939)
                      ·
                        rfl

theorem cell23_2170526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_2170526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2170526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2170526 prefixEnd_2170526 := by exact prefixLift 2170526
  have htrace : WordTrace (prefixWord ++ tailWord_2170526) baseStart_2170526 baseEnd_2170526 := by
    simpa [prefixWord, tailWord_2170526, baseEnd_2170526] using wordTrace_append hprefix tailTrace_2170526
  have hstable : (prefixWord ++ tailWord_2170526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170526).length < 2 ^ (prefixWord ++ tailWord_2170526).sum := by decide
  have hdescent : baseEnd_2170526 < baseStart_2170526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170549 : List Nat := [1, 3, 3, 3, 2, 2, 1, 1, 7]
def baseStart_2170549 : Nat := 118140960795 + 2170549 * 2 ^ 59
def prefixEnd_2170549 : Nat := 4983230072969 + 3 ^ 40 * 2170549 * 2
def baseEnd_2170549 : Nat := 123837213459548161195037

theorem tailTrace_2170549 : CollatzResearch.WordTrace tailWord_2170549 prefixEnd_2170549 123837213459548161195037 := by
  unfold tailWord_2170549
  simp only [CollatzResearch.WordTrace]
  refine ⟨79166425813479148101354701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52777617208986098734236467 79166425813479148101354701)
  ·
    refine ⟨29687409680054680538008013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79166425813479148101354701 29687409680054680538008013)
    ·
      refine ⟨11132778630020505201753005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29687409680054680538008013 11132778630020505201753005)
      ·
        refine ⟨4174791986257689450657377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11132778630020505201753005 4174791986257689450657377)
        ·
          refine ⟨3131093989693267087993033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4174791986257689450657377 3131093989693267087993033)
          ·
            refine ⟨2348320492269950315994775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3131093989693267087993033 2348320492269950315994775)
            ·
              refine ⟨3522480738404925473992163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2348320492269950315994775 3522480738404925473992163)
              ·
                refine ⟨5283721107607388210988245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3522480738404925473992163 5283721107607388210988245)
                ·
                  refine ⟨123837213459548161195037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5283721107607388210988245 123837213459548161195037)
                  ·
                    rfl

theorem cell23_2170549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 1, 7].length) (baseStart_2170549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2170549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2170549 prefixEnd_2170549 := by exact prefixLift 2170549
  have htrace : WordTrace (prefixWord ++ tailWord_2170549) baseStart_2170549 baseEnd_2170549 := by
    simpa [prefixWord, tailWord_2170549, baseEnd_2170549] using wordTrace_append hprefix tailTrace_2170549
  have hstable : (prefixWord ++ tailWord_2170549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170549).length < 2 ^ (prefixWord ++ tailWord_2170549).sum := by decide
  have hdescent : baseEnd_2170549 < baseStart_2170549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170630 : List Nat := [6, 2, 2, 1, 1, 1, 1, 1, 1, 7]
def baseStart_2170630 : Nat := 118140960795 + 2170630 * 2 ^ 59
def prefixEnd_2170630 : Nat := 4983230072969 + 3 ^ 40 * 2170630 * 2
def baseEnd_2170630 : Nat := 371525504356315877947487

theorem tailTrace_2170630 : CollatzResearch.WordTrace tailWord_2170630 prefixEnd_2170630 371525504356315877947487 := by
  unfold tailWord_2170630
  simp only [CollatzResearch.WordTrace]
  refine ⟨2474043128943303091720417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 52779586750790465956702229 2474043128943303091720417)
  ·
    refine ⟨1855532346707477318790313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2474043128943303091720417 1855532346707477318790313)
    ·
      refine ⟨1391649260030607989092735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1855532346707477318790313 1391649260030607989092735)
      ·
        refine ⟨2087473890045911983639103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1391649260030607989092735 2087473890045911983639103)
        ·
          refine ⟨3131210835068867975458655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2087473890045911983639103 3131210835068867975458655)
          ·
            refine ⟨4696816252603301963187983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3131210835068867975458655 4696816252603301963187983)
            ·
              refine ⟨7045224378904952944781975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4696816252603301963187983 7045224378904952944781975)
              ·
                refine ⟨10567836568357429417172963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7045224378904952944781975 10567836568357429417172963)
                ·
                  refine ⟨15851754852536144125759445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10567836568357429417172963 15851754852536144125759445)
                  ·
                    refine ⟨371525504356315877947487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15851754852536144125759445 371525504356315877947487)
                    ·
                      rfl

theorem cell23_2170630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_2170630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2170630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2170630 prefixEnd_2170630 := by exact prefixLift 2170630
  have htrace : WordTrace (prefixWord ++ tailWord_2170630) baseStart_2170630 baseEnd_2170630 := by
    simpa [prefixWord, tailWord_2170630, baseEnd_2170630] using wordTrace_append hprefix tailTrace_2170630
  have hstable : (prefixWord ++ tailWord_2170630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170630).length < 2 ^ (prefixWord ++ tailWord_2170630).sum := by decide
  have hdescent : baseEnd_2170630 < baseStart_2170630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170659 : List Nat := [1, 1, 1, 4, 2, 1, 2, 4, 2, 3, 2]
def baseStart_2170659 : Nat := 118140960795 + 2170659 * 2 ^ 59
def prefixEnd_2170659 : Nat := 4983230072969 + 3 ^ 40 * 2170659 * 2
def baseEnd_2170659 : Nat := 1114591404007928020379827

theorem tailTrace_2170659 : CollatzResearch.WordTrace tailWord_2170659 prefixEnd_2170659 1114591404007928020379827 := by
  unfold tailWord_2170659
  simp only [CollatzResearch.WordTrace]
  refine ⟨79170437843080636887859031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52780291895387091258572687 79170437843080636887859031)
  ·
    refine ⟨118755656764620955331788547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79170437843080636887859031 118755656764620955331788547)
    ·
      refine ⟨178133485146931432997682821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118755656764620955331788547 178133485146931432997682821)
      ·
        refine ⟨33400028465049643687065529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 178133485146931432997682821 33400028465049643687065529)
        ·
          refine ⟨25050021348787232765299147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33400028465049643687065529 25050021348787232765299147)
          ·
            refine ⟨37575032023180849147948721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25050021348787232765299147 37575032023180849147948721)
            ·
              refine ⟨28181274017385636860961541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37575032023180849147948721 28181274017385636860961541)
              ·
                refine ⟨5283988878259806911430289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28181274017385636860961541 5283988878259806911430289)
                ·
                  refine ⟨3962991658694855183572717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5283988878259806911430289 3962991658694855183572717)
                  ·
                    refine ⟨1486121872010570693839769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3962991658694855183572717 1486121872010570693839769)
                    ·
                      refine ⟨1114591404007928020379827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1486121872010570693839769 1114591404007928020379827)
                      ·
                        rfl

theorem cell23_2170659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4, 2, 3, 2].length) (baseStart_2170659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2170659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2170659 prefixEnd_2170659 := by exact prefixLift 2170659
  have htrace : WordTrace (prefixWord ++ tailWord_2170659) baseStart_2170659 baseEnd_2170659 := by
    simpa [prefixWord, tailWord_2170659, baseEnd_2170659] using wordTrace_append hprefix tailTrace_2170659
  have hstable : (prefixWord ++ tailWord_2170659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170659).length < 2 ^ (prefixWord ++ tailWord_2170659).sum := by decide
  have hdescent : baseEnd_2170659 < baseStart_2170659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170676 : List Nat := [2, 5, 1, 1, 2, 1, 1, 2, 1, 5, 2]
def baseStart_2170676 : Nat := 118140960795 + 2170676 * 2 ^ 59
def prefixEnd_2170676 : Nat := 4983230072969 + 3 ^ 40 * 2170676 * 2
def baseEnd_2170676 : Nat := 1114600133179054453867249

theorem tailTrace_2170676 : CollatzResearch.WordTrace tailWord_2170676 prefixEnd_2170676 1114600133179054453867249 := by
  unfold tailWord_2170676
  simp only [CollatzResearch.WordTrace]
  refine ⟨39585528942009524395613941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52780705256012699194151921 39585528942009524395613941)
  ·
    refine ⟨3711143338313392912088807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39585528942009524395613941 3711143338313392912088807)
    ·
      refine ⟨5566715007470089368133211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3711143338313392912088807 5566715007470089368133211)
      ·
        refine ⟨8350072511205134052199817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5566715007470089368133211 8350072511205134052199817)
        ·
          refine ⟨6262554383403850539149863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8350072511205134052199817 6262554383403850539149863)
          ·
            refine ⟨9393831575105775808724795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6262554383403850539149863 9393831575105775808724795)
            ·
              refine ⟨14090747362658663713087193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9393831575105775808724795 14090747362658663713087193)
              ·
                refine ⟨10568060521993997784815395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14090747362658663713087193 10568060521993997784815395)
                ·
                  refine ⟨15852090782990996677223093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10568060521993997784815395 15852090782990996677223093)
                  ·
                    refine ⟨1486133510905405938489665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15852090782990996677223093 1486133510905405938489665)
                    ·
                      refine ⟨1114600133179054453867249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1486133510905405938489665 1114600133179054453867249)
                      ·
                        rfl

theorem cell23_2170676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_2170676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2170676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2170676 prefixEnd_2170676 := by exact prefixLift 2170676
  have htrace : WordTrace (prefixWord ++ tailWord_2170676) baseStart_2170676 baseEnd_2170676 := by
    simpa [prefixWord, tailWord_2170676, baseEnd_2170676] using wordTrace_append hprefix tailTrace_2170676
  have hstable : (prefixWord ++ tailWord_2170676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170676).length < 2 ^ (prefixWord ++ tailWord_2170676).sum := by decide
  have hdescent : baseEnd_2170676 < baseStart_2170676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170686 : List Nat := [4, 2, 1, 2, 2, 2, 2, 2, 1, 5]
def baseStart_2170686 : Nat := 118140960795 + 2170686 * 2 ^ 59
def prefixEnd_2170686 : Nat := 4983230072969 + 3 ^ 40 * 2170686 * 2
def baseEnd_2170686 : Nat := 371535089328533138247401

theorem tailTrace_2170686 : CollatzResearch.WordTrace tailWord_2170686 prefixEnd_2170686 371535089328533138247401 := by
  unfold tailWord_2170686
  simp only [CollatzResearch.WordTrace]
  refine ⟨9896427826747852562386489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52780948409321880332727941 9896427826747852562386489)
  ·
    refine ⟨7422320870060889421789867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9896427826747852562386489 7422320870060889421789867)
    ·
      refine ⟨11133481305091334132684801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7422320870060889421789867 11133481305091334132684801)
      ·
        refine ⟨8350110978818500599513601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11133481305091334132684801 8350110978818500599513601)
        ·
          refine ⟨6262583234113875449635201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8350110978818500599513601 6262583234113875449635201)
          ·
            refine ⟨4696937425585406587226401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6262583234113875449635201 4696937425585406587226401)
            ·
              refine ⟨3522703069189054940419801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4696937425585406587226401 3522703069189054940419801)
              ·
                refine ⟨2642027301891791205314851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3522703069189054940419801 2642027301891791205314851)
                ·
                  refine ⟨3963040952837686807972277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2642027301891791205314851 3963040952837686807972277)
                  ·
                    refine ⟨371535089328533138247401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3963040952837686807972277 371535089328533138247401)
                    ·
                      rfl

theorem cell23_2170686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_2170686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2170686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2170686 prefixEnd_2170686 := by exact prefixLift 2170686
  have htrace : WordTrace (prefixWord ++ tailWord_2170686) baseStart_2170686 baseEnd_2170686 := by
    simpa [prefixWord, tailWord_2170686, baseEnd_2170686] using wordTrace_append hprefix tailTrace_2170686
  have hstable : (prefixWord ++ tailWord_2170686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170686).length < 2 ^ (prefixWord ++ tailWord_2170686).sum := by decide
  have hdescent : baseEnd_2170686 < baseStart_2170686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170700 : List Nat := [2, 2, 1, 3, 4, 2, 1, 3, 1, 1, 3]
def baseStart_2170700 : Nat := 118140960795 + 2170700 * 2 ^ 59
def prefixEnd_2170700 : Nat := 4983230072969 + 3 ^ 40 * 2170700 * 2
def baseEnd_2170700 : Nat := 1114612456714762359967139

theorem tailTrace_2170700 : CollatzResearch.WordTrace tailWord_2170700 prefixEnd_2170700 1114612456714762359967139 := by
  unfold tailWord_2170700
  simp only [CollatzResearch.WordTrace]
  refine ⟨39585966617966050445050777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52781288823954733926734369 39585966617966050445050777)
  ·
    refine ⟨29689474963474537833788083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39585966617966050445050777 29689474963474537833788083)
    ·
      refine ⟨44534212445211806750682125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29689474963474537833788083 44534212445211806750682125)
      ·
        refine ⟨16700329666954427531505797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44534212445211806750682125 16700329666954427531505797)
        ·
          refine ⟨3131311812553955162157337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16700329666954427531505797 3131311812553955162157337)
          ·
            refine ⟨2348483859415466371618003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3131311812553955162157337 2348483859415466371618003)
            ·
              refine ⟨3522725789123199557427005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2348483859415466371618003 3522725789123199557427005)
              ·
                refine ⟨1321022170921199834035127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3522725789123199557427005 1321022170921199834035127)
                ·
                  refine ⟨1981533256381799751052691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1321022170921199834035127 1981533256381799751052691)
                  ·
                    refine ⟨2972299884572699626579037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1981533256381799751052691 2972299884572699626579037)
                    ·
                      refine ⟨1114612456714762359967139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2972299884572699626579037 1114612456714762359967139)
                      ·
                        rfl

theorem cell23_2170700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 3, 1, 1, 3].length) (baseStart_2170700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2170700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2170700 prefixEnd_2170700 := by exact prefixLift 2170700
  have htrace : WordTrace (prefixWord ++ tailWord_2170700) baseStart_2170700 baseEnd_2170700 := by
    simpa [prefixWord, tailWord_2170700, baseEnd_2170700] using wordTrace_append hprefix tailTrace_2170700
  have hstable : (prefixWord ++ tailWord_2170700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170700).length < 2 ^ (prefixWord ++ tailWord_2170700).sum := by decide
  have hdescent : baseEnd_2170700 < baseStart_2170700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170709 : List Nat := [1, 3, 2, 2, 2, 3, 2, 1, 1, 1, 5]
def baseStart_2170709 : Nat := 118140960795 + 2170709 * 2 ^ 59
def prefixEnd_2170709 : Nat := 4983230072969 + 3 ^ 40 * 2170709 * 2
def baseEnd_2170709 : Nat := 1114617078040652824754597

theorem tailTrace_2170709 : CollatzResearch.WordTrace tailWord_2170709 prefixEnd_2170709 1114617078040652824754597 := by
  unfold tailWord_2170709
  simp only [CollatzResearch.WordTrace]
  refine ⟨79172261492899495427179181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52781507661932996951452787 79172261492899495427179181)
  ·
    refine ⟨29689598059837310785192193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79172261492899495427179181 29689598059837310785192193)
    ·
      refine ⟨22267198544877983088894145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29689598059837310785192193 22267198544877983088894145)
      ·
        refine ⟨16700398908658487316670609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22267198544877983088894145 16700398908658487316670609)
        ·
          refine ⟨12525299181493865487502957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16700398908658487316670609 12525299181493865487502957)
          ·
            refine ⟨4696987193060199557813609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12525299181493865487502957 4696987193060199557813609)
            ·
              refine ⟨3522740394795149668360207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4696987193060199557813609 3522740394795149668360207)
              ·
                refine ⟨5284110592192724502540311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3522740394795149668360207 5284110592192724502540311)
                ·
                  refine ⟨7926165888289086753810467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5284110592192724502540311 7926165888289086753810467)
                  ·
                    refine ⟨11889248832433630130715701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7926165888289086753810467 11889248832433630130715701)
                    ·
                      refine ⟨1114617078040652824754597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11889248832433630130715701 1114617078040652824754597)
                      ·
                        rfl

theorem cell23_2170709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_2170709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2170709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2170709 prefixEnd_2170709 := by exact prefixLift 2170709
  have htrace : WordTrace (prefixWord ++ tailWord_2170709) baseStart_2170709 baseEnd_2170709 := by
    simpa [prefixWord, tailWord_2170709, baseEnd_2170709] using wordTrace_append hprefix tailTrace_2170709
  have hstable : (prefixWord ++ tailWord_2170709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170709).length < 2 ^ (prefixWord ++ tailWord_2170709).sum := by decide
  have hdescent : baseEnd_2170709 < baseStart_2170709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170836 : List Nat := [2, 4, 1, 2, 1, 1, 1, 6, 5]
def baseStart_2170836 : Nat := 118140960795 + 2170836 * 2 ^ 59
def prefixEnd_2170836 : Nat := 4983230072969 + 3 ^ 40 * 2170836 * 2
def baseEnd_2170836 : Nat := 123853587787085980874057

theorem tailTrace_2170836 : CollatzResearch.WordTrace tailWord_2170836 prefixEnd_2170836 123853587787085980874057 := by
  unfold tailWord_2170836
  simp only [CollatzResearch.WordTrace]
  refine ⟨39588446781719698058526181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52784595708959597411368241 39588446781719698058526181)
  ·
    refine ⟨7422833771572443385973659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39588446781719698058526181 7422833771572443385973659)
    ·
      refine ⟨11134250657358665078960489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7422833771572443385973659 11134250657358665078960489)
      ·
        refine ⟨8350687993018998809220367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11134250657358665078960489 8350687993018998809220367)
        ·
          refine ⟨12526031989528498213830551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8350687993018998809220367 12526031989528498213830551)
          ·
            refine ⟨18789047984292747320745827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12526031989528498213830551 18789047984292747320745827)
            ·
              refine ⟨28183571976439120981118741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18789047984292747320745827 28183571976439120981118741)
              ·
                refine ⟨1321104936395583795989941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28183571976439120981118741 1321104936395583795989941)
                ·
                  refine ⟨123853587787085980874057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1321104936395583795989941 123853587787085980874057)
                  ·
                    rfl

theorem cell23_2170836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 6, 5].length) (baseStart_2170836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2170836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2170836 prefixEnd_2170836 := by exact prefixLift 2170836
  have htrace : WordTrace (prefixWord ++ tailWord_2170836) baseStart_2170836 baseEnd_2170836 := by
    simpa [prefixWord, tailWord_2170836, baseEnd_2170836] using wordTrace_append hprefix tailTrace_2170836
  have hstable : (prefixWord ++ tailWord_2170836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170836).length < 2 ^ (prefixWord ++ tailWord_2170836).sum := by decide
  have hdescent : baseEnd_2170836 < baseStart_2170836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170870 : List Nat := [5, 1, 1, 1, 4, 2, 1, 3, 5]
def baseStart_2170870 : Nat := 118140960795 + 2170870 * 2 ^ 59
def prefixEnd_2170870 : Nat := 4983230072969 + 3 ^ 40 * 2170870 * 2
def baseEnd_2170870 : Nat := 123855527602891854982373

theorem tailTrace_2170870 : CollatzResearch.WordTrace tailWord_2170870 prefixEnd_2170870 123855527602891854982373 := by
  unfold tailWord_2170870
  simp only [CollatzResearch.WordTrace]
  refine ⟨4948633352832263745236879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52785422430210813282526709 4948633352832263745236879)
  ·
    refine ⟨7422950029248395617855319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4948633352832263745236879 7422950029248395617855319)
    ·
      refine ⟨11134425043872593426782979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7422950029248395617855319 11134425043872593426782979)
      ·
        refine ⟨16701637565808890140174469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11134425043872593426782979 16701637565808890140174469)
        ·
          refine ⟨3131557043589166901282713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16701637565808890140174469 3131557043589166901282713)
          ·
            refine ⟨2348667782691875175962035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3131557043589166901282713 2348667782691875175962035)
            ·
              refine ⟨3523001674037812763943053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2348667782691875175962035 3523001674037812763943053)
              ·
                refine ⟨1321125627764179786478645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3523001674037812763943053 1321125627764179786478645)
                ·
                  refine ⟨123855527602891854982373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1321125627764179786478645 123855527602891854982373)
                  ·
                    rfl

theorem cell23_2170870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 3, 5].length) (baseStart_2170870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2170870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2170870 prefixEnd_2170870 := by exact prefixLift 2170870
  have htrace : WordTrace (prefixWord ++ tailWord_2170870) baseStart_2170870 baseEnd_2170870 := by
    simpa [prefixWord, tailWord_2170870, baseEnd_2170870] using wordTrace_append hprefix tailTrace_2170870
  have hstable : (prefixWord ++ tailWord_2170870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170870).length < 2 ^ (prefixWord ++ tailWord_2170870).sum := by decide
  have hdescent : baseEnd_2170870 < baseStart_2170870 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170879 : List Nat := [1, 1, 2, 2, 1, 2, 1, 4, 5, 4]
def baseStart_2170879 : Nat := 118140960795 + 2170879 * 2 ^ 59
def prefixEnd_2170879 : Nat := 4983230072969 + 3 ^ 40 * 2170879 * 2
def baseEnd_2170879 : Nat := 371568123250639053209605

theorem tailTrace_2170879 : CollatzResearch.WordTrace tailWord_2170879 prefixEnd_2170879 371568123250639053209605 := by
  unfold tailWord_2170879
  simp only [CollatzResearch.WordTrace]
  refine ⟨79178461902283614460867691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52785641268189076307245127 79178461902283614460867691)
  ·
    refine ⟨118767692853425421691301537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79178461902283614460867691 118767692853425421691301537)
    ·
      refine ⟨89075769640069066268476153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118767692853425421691301537 89075769640069066268476153)
      ·
        refine ⟨66806827230051799701357115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89075769640069066268476153 66806827230051799701357115)
        ·
          refine ⟨100210240845077699552035673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66806827230051799701357115 100210240845077699552035673)
          ·
            refine ⟨75157680633808274664026755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100210240845077699552035673 75157680633808274664026755)
            ·
              refine ⟨112736520950712411996040133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75157680633808274664026755 112736520950712411996040133)
              ·
                refine ⟨21138097678258577249257525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 112736520950712411996040133 21138097678258577249257525)
                ·
                  refine ⟨1981696657336741617117893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21138097678258577249257525 1981696657336741617117893)
                  ·
                    refine ⟨371568123250639053209605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1981696657336741617117893 371568123250639053209605)
                    ·
                      rfl

theorem cell23_2170879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 5, 4].length) (baseStart_2170879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2170879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2170879 prefixEnd_2170879 := by exact prefixLift 2170879
  have htrace : WordTrace (prefixWord ++ tailWord_2170879) baseStart_2170879 baseEnd_2170879 := by
    simpa [prefixWord, tailWord_2170879, baseEnd_2170879] using wordTrace_append hprefix tailTrace_2170879
  have hstable : (prefixWord ++ tailWord_2170879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170879).length < 2 ^ (prefixWord ++ tailWord_2170879).sum := by decide
  have hdescent : baseEnd_2170879 < baseStart_2170879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170920 : List Nat := [2, 1, 5, 3, 1, 1, 2, 1, 2, 1, 4]
def baseStart_2170920 : Nat := 118140960795 + 2170920 * 2 ^ 59
def prefixEnd_2170920 : Nat := 4983230072969 + 3 ^ 40 * 2170920 * 2
def baseEnd_2170920 : Nat := 1114725422458751499216127

theorem tailTrace_2170920 : CollatzResearch.WordTrace tailWord_2170920 prefixEnd_2170920 1114725422458751499216127 := by
  unfold tailWord_2170920
  simp only [CollatzResearch.WordTrace]
  refine ⟨39589978647567539231555107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52786638196756718975406809 39589978647567539231555107)
  ·
    refine ⟨59384967971351308847332661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39589978647567539231555107 59384967971351308847332661)
    ·
      refine ⟨5567340747314185204437437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59384967971351308847332661 5567340747314185204437437)
      ·
        refine ⟨2087752780242819451664039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5567340747314185204437437 2087752780242819451664039)
        ·
          refine ⟨3131629170364229177496059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2087752780242819451664039 3131629170364229177496059)
          ·
            refine ⟨4697443755546343766244089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3131629170364229177496059 4697443755546343766244089)
            ·
              refine ⟨3523082816659757824683067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4697443755546343766244089 3523082816659757824683067)
              ·
                refine ⟨5284624224989636737024601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3523082816659757824683067 5284624224989636737024601)
                ·
                  refine ⟨3963468168742227552768451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5284624224989636737024601 3963468168742227552768451)
                  ·
                    refine ⟨5945202253113341329152677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3963468168742227552768451 5945202253113341329152677)
                    ·
                      refine ⟨1114725422458751499216127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5945202253113341329152677 1114725422458751499216127)
                      ·
                        rfl

theorem cell23_2170920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_2170920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2170920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2170920 prefixEnd_2170920 := by exact prefixLift 2170920
  have htrace : WordTrace (prefixWord ++ tailWord_2170920) baseStart_2170920 baseEnd_2170920 := by
    simpa [prefixWord, tailWord_2170920, baseEnd_2170920] using wordTrace_append hprefix tailTrace_2170920
  have hstable : (prefixWord ++ tailWord_2170920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170920).length < 2 ^ (prefixWord ++ tailWord_2170920).sum := by decide
  have hdescent : baseEnd_2170920 < baseStart_2170920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170973 : List Nat := [1, 4, 4, 1, 1, 1, 2, 1, 3, 5]
def baseStart_2170973 : Nat := 118140960795 + 2170973 * 2 ^ 59
def prefixEnd_2170973 : Nat := 4983230072969 + 3 ^ 40 * 2170973 * 2
def baseEnd_2170973 : Nat := 371584212311146597284461

theorem tailTrace_2170973 : CollatzResearch.WordTrace tailWord_2170973 prefixEnd_2170973 371584212311146597284461 := by
  unfold tailWord_2170973
  simp only [CollatzResearch.WordTrace]
  refine ⟨79181890363943068514789573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52787926909295379009859715 79181890363943068514789573)
  ·
    refine ⟨14846604443239325346523045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79181890363943068514789573 14846604443239325346523045)
    ·
      refine ⟨2783738333107373502473071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14846604443239325346523045 2783738333107373502473071)
      ·
        refine ⟨4175607499661060253709607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2783738333107373502473071 4175607499661060253709607)
        ·
          refine ⟨6263411249491590380564411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4175607499661060253709607 6263411249491590380564411)
          ·
            refine ⟨9395116874237385570846617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6263411249491590380564411 9395116874237385570846617)
            ·
              refine ⟨7046337655678039178134963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9395116874237385570846617 7046337655678039178134963)
              ·
                refine ⟨10569506483517058767202445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7046337655678039178134963 10569506483517058767202445)
                ·
                  refine ⟨3963564931318897037700917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10569506483517058767202445 3963564931318897037700917)
                  ·
                    refine ⟨371584212311146597284461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3963564931318897037700917 371584212311146597284461)
                    ·
                      rfl

theorem cell23_2170973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_2170973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2170973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2170973 prefixEnd_2170973 := by exact prefixLift 2170973
  have htrace : WordTrace (prefixWord ++ tailWord_2170973) baseStart_2170973 baseEnd_2170973 := by
    simpa [prefixWord, tailWord_2170973, baseEnd_2170973] using wordTrace_append hprefix tailTrace_2170973
  have hstable : (prefixWord ++ tailWord_2170973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170973).length < 2 ^ (prefixWord ++ tailWord_2170973).sum := by decide
  have hdescent : baseEnd_2170973 < baseStart_2170973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170974 : List Nat := [4, 4, 1, 1, 2, 2, 1, 1, 2, 2, 3]
def baseStart_2170974 : Nat := 118140960795 + 2170974 * 2 ^ 59
def prefixEnd_2170974 : Nat := 4983230072969 + 3 ^ 40 * 2170974 * 2
def baseEnd_2170974 : Nat := 1114753150414094287940879

theorem tailTrace_2170974 : CollatzResearch.WordTrace tailWord_2170974 prefixEnd_2170974 1114753150414094287940879 := by
  unfold tailWord_2170974
  simp only [CollatzResearch.WordTrace]
  refine ⟨9897740854617430710696997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52787951224626297123717317 9897740854617430710696997)
  ·
    refine ⟨1855826410240768258255687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9897740854617430710696997 1855826410240768258255687)
    ·
      refine ⟨2783739615361152387383531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1855826410240768258255687 2783739615361152387383531)
      ·
        refine ⟨4175609423041728581075297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2783739615361152387383531 4175609423041728581075297)
        ·
          refine ⟨3131707067281296435806473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4175609423041728581075297 3131707067281296435806473)
          ·
            refine ⟨2348780300460972326854855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3131707067281296435806473 2348780300460972326854855)
            ·
              refine ⟨3523170450691458490282283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2348780300460972326854855 3523170450691458490282283)
              ·
                refine ⟨5284755676037187735423425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3523170450691458490282283 5284755676037187735423425)
                ·
                  refine ⟨3963566757027890801567569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5284755676037187735423425 3963566757027890801567569)
                  ·
                    refine ⟨2972675067770918101175677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3963566757027890801567569 2972675067770918101175677)
                    ·
                      refine ⟨1114753150414094287940879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2972675067770918101175677 1114753150414094287940879)
                      ·
                        rfl

theorem cell23_2170974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_2170974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2170974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2170974 prefixEnd_2170974 := by exact prefixLift 2170974
  have htrace : WordTrace (prefixWord ++ tailWord_2170974) baseStart_2170974 baseEnd_2170974 := by
    simpa [prefixWord, tailWord_2170974, baseEnd_2170974] using wordTrace_append hprefix tailTrace_2170974
  have hstable : (prefixWord ++ tailWord_2170974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170974).length < 2 ^ (prefixWord ++ tailWord_2170974).sum := by decide
  have hdescent : baseEnd_2170974 < baseStart_2170974 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170976 : List Nat := [2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 4]
def baseStart_2170976 : Nat := 118140960795 + 2170976 * 2 ^ 59
def prefixEnd_2170976 : Nat := 4983230072969 + 3 ^ 40 * 2170976 * 2
def baseEnd_2170976 : Nat := 1114754177375403280115869

theorem tailTrace_2170976 : CollatzResearch.WordTrace tailWord_2170976 prefixEnd_2170976 1114754177375403280115869 := by
  unfold tailWord_2170976
  simp only [CollatzResearch.WordTrace]
  refine ⟨39590999891466100013574391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52787999855288133351432521 39590999891466100013574391)
  ·
    refine ⟨59386499837199150020361587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39590999891466100013574391 59386499837199150020361587)
    ·
      refine ⟨89079749755798725030542381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59386499837199150020361587 89079749755798725030542381)
      ·
        refine ⟨33404906158424521886453393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89079749755798725030542381 33404906158424521886453393)
        ·
          refine ⟨25053679618818391414840045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33404906158424521886453393 25053679618818391414840045)
          ·
            refine ⟨9395129857056896780565017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25053679618818391414840045 9395129857056896780565017)
            ·
              refine ⟨7046347392792672585423763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9395129857056896780565017 7046347392792672585423763)
              ·
                refine ⟨10569521089189008878135645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7046347392792672585423763 10569521089189008878135645)
                ·
                  refine ⟨3963570408445878329300867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10569521089189008878135645 3963570408445878329300867)
                  ·
                    refine ⟨5945355612668817493951301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3963570408445878329300867 5945355612668817493951301)
                    ·
                      refine ⟨1114754177375403280115869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5945355612668817493951301 1114754177375403280115869)
                      ·
                        rfl

theorem cell23_2170976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 4].length) (baseStart_2170976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2170976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2170976 prefixEnd_2170976 := by exact prefixLift 2170976
  have htrace : WordTrace (prefixWord ++ tailWord_2170976) baseStart_2170976 baseEnd_2170976 := by
    simpa [prefixWord, tailWord_2170976, baseEnd_2170976] using wordTrace_append hprefix tailTrace_2170976
  have hstable : (prefixWord ++ tailWord_2170976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170976).length < 2 ^ (prefixWord ++ tailWord_2170976).sum := by decide
  have hdescent : baseEnd_2170976 < baseStart_2170976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170993 : List Nat := [1, 2, 2, 2, 1, 1, 3, 2, 5, 2, 2]
def baseStart_2170993 : Nat := 118140960795 + 2170993 * 2 ^ 59
def prefixEnd_2170993 : Nat := 4983230072969 + 3 ^ 40 * 2170993 * 2
def baseEnd_2170993 : Nat := 1114762906546529713603291

theorem tailTrace_2170993 : CollatzResearch.WordTrace tailWord_2170993 prefixEnd_2170993 1114762906546529713603291 := by
  unfold tailWord_2170993
  simp only [CollatzResearch.WordTrace]
  refine ⟨79182619823870611930517633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52788413215913741287011755 79182619823870611930517633)
  ·
    refine ⟨59386964867902958947888225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79182619823870611930517633 59386964867902958947888225)
    ·
      refine ⟨44540223650927219210916169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59386964867902958947888225 44540223650927219210916169)
      ·
        refine ⟨33405167738195414408187127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44540223650927219210916169 33405167738195414408187127)
        ·
          refine ⟨50107751607293121612280691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33405167738195414408187127 50107751607293121612280691)
          ·
            refine ⟨75161627410939682418421037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50107751607293121612280691 75161627410939682418421037)
            ·
              refine ⟨28185610279102380906907889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75161627410939682418421037 28185610279102380906907889)
              ·
                refine ⟨21139207709326785680180917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28185610279102380906907889 21139207709326785680180917)
                ·
                  refine ⟨1981800722749386157516961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21139207709326785680180917 1981800722749386157516961)
                  ·
                    refine ⟨1486350542062039618137721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1981800722749386157516961 1486350542062039618137721)
                    ·
                      refine ⟨1114762906546529713603291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1486350542062039618137721 1114762906546529713603291)
                      ·
                        rfl

theorem cell23_2170993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 5, 2, 2].length) (baseStart_2170993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2170993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2170993 prefixEnd_2170993 := by exact prefixLift 2170993
  have htrace : WordTrace (prefixWord ++ tailWord_2170993) baseStart_2170993 baseEnd_2170993 := by
    simpa [prefixWord, tailWord_2170993, baseEnd_2170993] using wordTrace_append hprefix tailTrace_2170993
  have hstable : (prefixWord ++ tailWord_2170993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170993).length < 2 ^ (prefixWord ++ tailWord_2170993).sum := by decide
  have hdescent : baseEnd_2170993 < baseStart_2170993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170999 : List Nat := [1, 1, 3, 1, 1, 6, 10]
def baseStart_2170999 : Nat := 118140960795 + 2170999 * 2 ^ 59
def prefixEnd_2170999 : Nat := 4983230072969 + 3 ^ 40 * 2170999 * 2
def baseEnd_2170999 : Nat := 13762543054696996174423

theorem tailTrace_2170999 : CollatzResearch.WordTrace tailWord_2170999 prefixEnd_2170999 13762543054696996174423 := by
  unfold tailWord_2170999
  simp only [CollatzResearch.WordTrace]
  refine ⟨79182838661848874955236051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52788559107899249970157367 79182838661848874955236051)
  ·
    refine ⟨118774257992773312432854077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79182838661848874955236051 118774257992773312432854077)
    ·
      refine ⟨44540346747289992162320279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118774257992773312432854077 44540346747289992162320279)
      ·
        refine ⟨66810520120934988243480419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44540346747289992162320279 66810520120934988243480419)
        ·
          refine ⟨100215780181402482365220629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66810520120934988243480419 100215780181402482365220629)
          ·
            refine ⟨4697614696003241360869717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 100215780181402482365220629 4697614696003241360869717)
            ·
              refine ⟨13762543054696996174423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4697614696003241360869717 13762543054696996174423)
              ·
                rfl

theorem cell23_2170999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 10].length) (baseStart_2170999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2170999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2170999 prefixEnd_2170999 := by exact prefixLift 2170999
  have htrace : WordTrace (prefixWord ++ tailWord_2170999) baseStart_2170999 baseEnd_2170999 := by
    simpa [prefixWord, tailWord_2170999, baseEnd_2170999] using wordTrace_append hprefix tailTrace_2170999
  have hstable : (prefixWord ++ tailWord_2170999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170999).length < 2 ^ (prefixWord ++ tailWord_2170999).sum := by decide
  have hdescent : baseEnd_2170999 < baseStart_2170999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171050 : List Nat := [3, 1, 5, 1, 3, 1, 9]
def baseStart_2171050 : Nat := 118140960795 + 2171050 * 2 ^ 59
def prefixEnd_2171050 : Nat := 4983230072969 + 3 ^ 40 * 2171050 * 2
def baseEnd_2171050 : Nat := 13762866357331308525809

theorem tailTrace_2171050 : CollatzResearch.WordTrace tailWord_2171050 prefixEnd_2171050 13762866357331308525809 := by
  unfold tailWord_2171050
  simp only [CollatzResearch.WordTrace]
  refine ⟨19796174696166027666335651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52789799189776073776895069 19796174696166027666335651)
  ·
    refine ⟨29694262044249041499503477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19796174696166027666335651 29694262044249041499503477)
    ·
      refine ⟨2783837066648347640578451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29694262044249041499503477 2783837066648347640578451)
      ·
        refine ⟨4175755599972521460867677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2783837066648347640578451 4175755599972521460867677)
        ·
          refine ⟨1565908349989695547825379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4175755599972521460867677 1565908349989695547825379)
          ·
            refine ⟨2348862524984543321738069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1565908349989695547825379 2348862524984543321738069)
            ·
              refine ⟨13762866357331308525809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2348862524984543321738069 13762866357331308525809)
              ·
                rfl

theorem cell23_2171050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 9].length) (baseStart_2171050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2171050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2171050 prefixEnd_2171050 := by exact prefixLift 2171050
  have htrace : WordTrace (prefixWord ++ tailWord_2171050) baseStart_2171050 baseEnd_2171050 := by
    simpa [prefixWord, tailWord_2171050, baseEnd_2171050] using wordTrace_append hprefix tailTrace_2171050
  have hstable : (prefixWord ++ tailWord_2171050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171050).length < 2 ^ (prefixWord ++ tailWord_2171050).sum := by decide
  have hdescent : baseEnd_2171050 < baseStart_2171050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171061 : List Nat := [1, 3, 3, 4, 2, 1, 1, 1, 3, 2, 2]
def baseStart_2171061 : Nat := 118140960795 + 2171061 * 2 ^ 59
def prefixEnd_2171061 : Nat := 4983230072969 + 3 ^ 40 * 2171061 * 2
def baseEnd_2171061 : Nat := 1114797823231035447552979

theorem tailTrace_2171061 : CollatzResearch.WordTrace tailWord_2171061 prefixEnd_2171061 1114797823231035447552979 := by
  unfold tailWord_2171061
  simp only [CollatzResearch.WordTrace]
  refine ⟨79185099987624259543993037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52790066658416173029328691 79185099987624259543993037)
  ·
    refine ⟨29694412495359097328997389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79185099987624259543993037 29694412495359097328997389)
    ·
      refine ⟨11135404685759661498374021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29694412495359097328997389 11135404685759661498374021)
      ·
        refine ⟨2087888378579936530945129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11135404685759661498374021 2087888378579936530945129)
        ·
          refine ⟨1565916283934952398208847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2087888378579936530945129 1565916283934952398208847)
          ·
            refine ⟨2348874425902428597313271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1565916283934952398208847 2348874425902428597313271)
            ·
              refine ⟨3523311638853642895969907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2348874425902428597313271 3523311638853642895969907)
              ·
                refine ⟨5284967458280464343954861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3523311638853642895969907 5284967458280464343954861)
                ·
                  refine ⟨1981862796855174128983073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5284967458280464343954861 1981862796855174128983073)
                  ·
                    refine ⟨1486397097641380596737305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1981862796855174128983073 1486397097641380596737305)
                    ·
                      refine ⟨1114797823231035447552979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1486397097641380596737305 1114797823231035447552979)
                      ·
                        rfl

theorem cell23_2171061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_2171061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2171061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2171061 prefixEnd_2171061 := by exact prefixLift 2171061
  have htrace : WordTrace (prefixWord ++ tailWord_2171061) baseStart_2171061 baseEnd_2171061 := by
    simpa [prefixWord, tailWord_2171061, baseEnd_2171061] using wordTrace_append hprefix tailTrace_2171061
  have hstable : (prefixWord ++ tailWord_2171061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171061).length < 2 ^ (prefixWord ++ tailWord_2171061).sum := by decide
  have hdescent : baseEnd_2171061 < baseStart_2171061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171083 : List Nat := [1, 1, 1, 1, 3, 2, 4, 3, 1, 4, 2]
def baseStart_2171083 : Nat := 118140960795 + 2171083 * 2 ^ 59
def prefixEnd_2171083 : Nat := 4983230072969 + 3 ^ 40 * 2171083 * 2
def baseEnd_2171083 : Nat := 1114809119805434361477877

theorem tailTrace_2171083 : CollatzResearch.WordTrace tailWord_2171083 prefixEnd_2171083 1114809119805434361477877 := by
  unfold tailWord_2171083
  simp only [CollatzResearch.WordTrace]
  refine ⟨79185902393544557301293903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52790601595696371534195935 79185902393544557301293903)
  ·
    refine ⟨118778853590316835951940855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79185902393544557301293903 118778853590316835951940855)
    ·
      refine ⟨178168280385475253927911283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118778853590316835951940855 178168280385475253927911283)
      ·
        refine ⟨267252420578212880891866925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178168280385475253927911283 267252420578212880891866925)
        ·
          refine ⟨100219657716829830334450097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 267252420578212880891866925 100219657716829830334450097)
          ·
            refine ⟨75164743287622372750837573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100219657716829830334450097 75164743287622372750837573)
            ·
              refine ⟨14093389366429194890782045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75164743287622372750837573 14093389366429194890782045)
              ·
                refine ⟨5285021012410948084043267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14093389366429194890782045 5285021012410948084043267)
                ·
                  refine ⟨7927531518616422126064901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5285021012410948084043267 7927531518616422126064901)
                  ·
                    refine ⟨1486412159740579148637169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7927531518616422126064901 1486412159740579148637169)
                    ·
                      refine ⟨1114809119805434361477877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1486412159740579148637169 1114809119805434361477877)
                      ·
                        rfl

theorem cell23_2171083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3, 1, 4, 2].length) (baseStart_2171083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2171083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2171083 prefixEnd_2171083 := by exact prefixLift 2171083
  have htrace : WordTrace (prefixWord ++ tailWord_2171083) baseStart_2171083 baseEnd_2171083 := by
    simpa [prefixWord, tailWord_2171083, baseEnd_2171083] using wordTrace_append hprefix tailTrace_2171083
  have hstable : (prefixWord ++ tailWord_2171083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171083).length < 2 ^ (prefixWord ++ tailWord_2171083).sum := by decide
  have hdescent : baseEnd_2171083 < baseStart_2171083 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171123 : List Nat := [1, 1, 1, 2, 2, 4, 3, 4, 5]
def baseStart_2171123 : Nat := 118140960795 + 2171123 * 2 ^ 59
def prefixEnd_2171123 : Nat := 4983230072969 + 3 ^ 40 * 2171123 * 2
def baseEnd_2171123 : Nat := 123869962114623800553077

theorem tailTrace_2171123 : CollatzResearch.WordTrace tailWord_2171123 prefixEnd_2171123 123869962114623800553077 := by
  unfold tailWord_2171123
  simp only [CollatzResearch.WordTrace]
  refine ⟨79187361313399644132750023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52791574208933096088500015 79187361313399644132750023)
  ·
    refine ⟨118781041970099466199125035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79187361313399644132750023 118781041970099466199125035)
    ·
      refine ⟨178171562955149199298687553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118781041970099466199125035 178171562955149199298687553)
      ·
        refine ⟨133628672216361899474015665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178171562955149199298687553 133628672216361899474015665)
        ·
          refine ⟨100221504162271424605511749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133628672216361899474015665 100221504162271424605511749)
          ·
            refine ⟨18791532030425892113533453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100221504162271424605511749 18791532030425892113533453)
            ·
              refine ⟨7046824511409709542575045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18791532030425892113533453 7046824511409709542575045)
              ·
                refine ⟨1321279595889320539232821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7046824511409709542575045 1321279595889320539232821)
                ·
                  refine ⟨123869962114623800553077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1321279595889320539232821 123869962114623800553077)
                  ·
                    rfl

theorem cell23_2171123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 4, 5].length) (baseStart_2171123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2171123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2171123 prefixEnd_2171123 := by exact prefixLift 2171123
  have htrace : WordTrace (prefixWord ++ tailWord_2171123) baseStart_2171123 baseEnd_2171123 := by
    simpa [prefixWord, tailWord_2171123, baseEnd_2171123] using wordTrace_append hprefix tailTrace_2171123
  have hstable : (prefixWord ++ tailWord_2171123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171123).length < 2 ^ (prefixWord ++ tailWord_2171123).sum := by decide
  have hdescent : baseEnd_2171123 < baseStart_2171123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171136 : List Nat := [2, 1, 1, 2, 1, 1, 4, 2, 4, 5]
def baseStart_2171136 : Nat := 118140960795 + 2171136 * 2 ^ 59
def prefixEnd_2171136 : Nat := 4983230072969 + 3 ^ 40 * 2171136 * 2
def baseEnd_2171136 : Nat := 371612111426707551371711

theorem tailTrace_2171136 : CollatzResearch.WordTrace tailWord_2171136 prefixEnd_2171136 371612111426707551371711 := by
  unfold tailWord_2171136
  simp only [CollatzResearch.WordTrace]
  refine ⟨39593917731176273676486631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52791890308235031568648841 39593917731176273676486631)
  ·
    refine ⟨59390876596764410514729947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39593917731176273676486631 59390876596764410514729947)
    ·
      refine ⟨89086314895146615772094921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59390876596764410514729947 89086314895146615772094921)
      ·
        refine ⟨66814736171359961829071191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89086314895146615772094921 66814736171359961829071191)
        ·
          refine ⟨100222104257039942743606787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66814736171359961829071191 100222104257039942743606787)
          ·
            refine ⟨150333156385559914115410181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100222104257039942743606787 150333156385559914115410181)
            ·
              refine ⟨28187466822292483896639409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 150333156385559914115410181 28187466822292483896639409)
              ·
                refine ⟨21140600116719362922479557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28187466822292483896639409 21140600116719362922479557)
                ·
                  refine ⟨3963862521884880547964917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21140600116719362922479557 3963862521884880547964917)
                  ·
                    refine ⟨371612111426707551371711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3963862521884880547964917 371612111426707551371711)
                    ·
                      rfl

theorem cell23_2171136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 4, 5].length) (baseStart_2171136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2171136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2171136 prefixEnd_2171136 := by exact prefixLift 2171136
  have htrace : WordTrace (prefixWord ++ tailWord_2171136) baseStart_2171136 baseEnd_2171136 := by
    simpa [prefixWord, tailWord_2171136, baseEnd_2171136] using wordTrace_append hprefix tailTrace_2171136
  have hstable : (prefixWord ++ tailWord_2171136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171136).length < 2 ^ (prefixWord ++ tailWord_2171136).sum := by decide
  have hdescent : baseEnd_2171136 < baseStart_2171136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171146 : List Nat := [3, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7]
def baseStart_2171146 : Nat := 118140960795 + 2171146 * 2 ^ 59
def prefixEnd_2171146 : Nat := 4983230072969 + 3 ^ 40 * 2171146 * 2
def baseEnd_2171146 : Nat := 1114841469086667614990087

theorem tailTrace_2171146 : CollatzResearch.WordTrace tailWord_2171146 prefixEnd_2171146 1114841469086667614990087 := by
  unfold tailWord_2171146
  simp only [CollatzResearch.WordTrace]
  refine ⟨19797050048079079765209323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52792133461544212707224861 19797050048079079765209323)
  ·
    refine ⟨29695575072118619647813985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19797050048079079765209323 29695575072118619647813985)
    ·
      refine ⟨22271681304088964735860489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29695575072118619647813985 22271681304088964735860489)
      ·
        refine ⟨16703760978066723551895367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22271681304088964735860489 16703760978066723551895367)
        ·
          refine ⟨25055641467100085327843051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16703760978066723551895367 25055641467100085327843051)
          ·
            refine ⟨37583462200650127991764577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25055641467100085327843051 37583462200650127991764577)
            ·
              refine ⟨28187596650487595993823433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37583462200650127991764577 28187596650487595993823433)
              ·
                refine ⟨21140697487865696995367575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28187596650487595993823433 21140697487865696995367575)
                ·
                  refine ⟨31711046231798545493051363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21140697487865696995367575 31711046231798545493051363)
                  ·
                    refine ⟨47566569347697818239577045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31711046231798545493051363 47566569347697818239577045)
                    ·
                      refine ⟨1114841469086667614990087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 47566569347697818239577045 1114841469086667614990087)
                      ·
                        rfl

theorem cell23_2171146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_2171146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2171146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2171146 prefixEnd_2171146 := by exact prefixLift 2171146
  have htrace : WordTrace (prefixWord ++ tailWord_2171146) baseStart_2171146 baseEnd_2171146 := by
    simpa [prefixWord, tailWord_2171146, baseEnd_2171146] using wordTrace_append hprefix tailTrace_2171146
  have hstable : (prefixWord ++ tailWord_2171146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171146).length < 2 ^ (prefixWord ++ tailWord_2171146).sum := by decide
  have hdescent : baseEnd_2171146 < baseStart_2171146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171153 : List Nat := [1, 2, 2, 1, 1, 5, 3, 1, 2, 5]
def baseStart_2171153 : Nat := 118140960795 + 2171153 * 2 ^ 59
def prefixEnd_2171153 : Nat := 4983230072969 + 3 ^ 40 * 2171153 * 2
def baseEnd_2171153 : Nat := 371615021150416362534185

theorem tailTrace_2171153 : CollatzResearch.WordTrace tailWord_2171153 prefixEnd_2171153 371615021150416362534185 := by
  unfold tailWord_2171153
  simp only [CollatzResearch.WordTrace]
  refine ⟨79188455503290959256342113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52792303668860639504228075 79188455503290959256342113)
  ·
    refine ⟨59391341627468219442256585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79188455503290959256342113 59391341627468219442256585)
    ·
      refine ⟨44543506220601164581692439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59391341627468219442256585 44543506220601164581692439)
      ·
        refine ⟨66815259330901746872538659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44543506220601164581692439 66815259330901746872538659)
        ·
          refine ⟨100222888996352620308807989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66815259330901746872538659 100222888996352620308807989)
          ·
            refine ⟨9395895843408058153950749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 100222888996352620308807989 9395895843408058153950749)
            ·
              refine ⟨3523460941278021807731531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9395895843408058153950749 3523460941278021807731531)
              ·
                refine ⟨5285191411917032711597297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3523460941278021807731531 5285191411917032711597297)
                ·
                  refine ⟨3963893558937774533697973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5285191411917032711597297 3963893558937774533697973)
                  ·
                    refine ⟨371615021150416362534185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3963893558937774533697973 371615021150416362534185)
                    ·
                      rfl

theorem cell23_2171153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 5].length) (baseStart_2171153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2171153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2171153 prefixEnd_2171153 := by exact prefixLift 2171153
  have htrace : WordTrace (prefixWord ++ tailWord_2171153) baseStart_2171153 baseEnd_2171153 := by
    simpa [prefixWord, tailWord_2171153, baseEnd_2171153] using wordTrace_append hprefix tailTrace_2171153
  have hstable : (prefixWord ++ tailWord_2171153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171153).length < 2 ^ (prefixWord ++ tailWord_2171153).sum := by decide
  have hdescent : baseEnd_2171153 < baseStart_2171153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171183 : List Nat := [1, 1, 2, 1, 2, 1, 5, 3, 3, 4]
def baseStart_2171183 : Nat := 118140960795 + 2171183 * 2 ^ 59
def prefixEnd_2171183 : Nat := 4983230072969 + 3 ^ 40 * 2171183 * 2
def baseEnd_2171183 : Nat := 371620155956961323409139

theorem tailTrace_2171183 : CollatzResearch.WordTrace tailWord_2171183 prefixEnd_2171183 371620155956961323409139 := by
  unfold tailWord_2171183
  simp only [CollatzResearch.WordTrace]
  refine ⟨79189549693182274379934203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52793033128788182919956135 79189549693182274379934203)
  ·
    refine ⟨118784324539773411569901305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79189549693182274379934203 118784324539773411569901305)
    ·
      refine ⟨89088243404830058677425979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118784324539773411569901305 89088243404830058677425979)
      ·
        refine ⟨133632365107245088016138969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89088243404830058677425979 133632365107245088016138969)
        ·
          refine ⟨100224273830433816012104227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133632365107245088016138969 100224273830433816012104227)
          ·
            refine ⟨150336410745650724018156341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100224273830433816012104227 150336410745650724018156341)
            ·
              refine ⟨14094038507404755376702157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 150336410745650724018156341 14094038507404755376702157)
              ·
                refine ⟨5285264440276783266263309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14094038507404755376702157 5285264440276783266263309)
                ·
                  refine ⟨1981974165103793724848741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5285264440276783266263309 1981974165103793724848741)
                  ·
                    refine ⟨371620155956961323409139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1981974165103793724848741 371620155956961323409139)
                    ·
                      rfl

theorem cell23_2171183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3, 3, 4].length) (baseStart_2171183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2171183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2171183 prefixEnd_2171183 := by exact prefixLift 2171183
  have htrace : WordTrace (prefixWord ++ tailWord_2171183) baseStart_2171183 baseEnd_2171183 := by
    simpa [prefixWord, tailWord_2171183, baseEnd_2171183] using wordTrace_append hprefix tailTrace_2171183
  have hstable : (prefixWord ++ tailWord_2171183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171183).length < 2 ^ (prefixWord ++ tailWord_2171183).sum := by decide
  have hdescent : baseEnd_2171183 < baseStart_2171183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171217 : List Nat := [1, 2, 2, 1, 4, 2, 3, 3, 1, 4]
def baseStart_2171217 : Nat := 118140960795 + 2171217 * 2 ^ 59
def prefixEnd_2171217 : Nat := 4983230072969 + 3 ^ 40 * 2171217 * 2
def baseEnd_2171217 : Nat := 371625975404378945734087

theorem tailTrace_2171217 : CollatzResearch.WordTrace tailWord_2171217 prefixEnd_2171217 371625975404378945734087 := by
  unfold tailWord_2171217
  simp only [CollatzResearch.WordTrace]
  refine ⟨79190789775059098186671905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52793859850039398791114603 79190789775059098186671905)
  ·
    refine ⟨59393092331294323640003929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79190789775059098186671905 59393092331294323640003929)
    ·
      refine ⟨44544819248470742730002947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59393092331294323640003929 44544819248470742730002947)
      ·
        refine ⟨66817228872706114095004421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44544819248470742730002947 66817228872706114095004421)
        ·
          refine ⟨12528230413632396392813329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66817228872706114095004421 12528230413632396392813329)
          ·
            refine ⟨9396172810224297294609997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12528230413632396392813329 9396172810224297294609997)
            ·
              refine ⟨3523564803834111485478749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9396172810224297294609997 3523564803834111485478749)
              ·
                refine ⟨1321336801437791807054531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3523564803834111485478749 1321336801437791807054531)
                ·
                  refine ⟨1982005202156687710581797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1321336801437791807054531 1982005202156687710581797)
                  ·
                    refine ⟨371625975404378945734087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1982005202156687710581797 371625975404378945734087)
                    ·
                      rfl

theorem cell23_2171217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 3, 1, 4].length) (baseStart_2171217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2171217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2171217 prefixEnd_2171217 := by exact prefixLift 2171217
  have htrace : WordTrace (prefixWord ++ tailWord_2171217) baseStart_2171217 baseEnd_2171217 := by
    simpa [prefixWord, tailWord_2171217, baseEnd_2171217] using wordTrace_append hprefix tailTrace_2171217
  have hstable : (prefixWord ++ tailWord_2171217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171217).length < 2 ^ (prefixWord ++ tailWord_2171217).sum := by decide
  have hdescent : baseEnd_2171217 < baseStart_2171217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171263 : List Nat := [1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 4]
def baseStart_2171263 : Nat := 118140960795 + 2171263 * 2 ^ 59
def prefixEnd_2171263 : Nat := 4983230072969 + 3 ^ 40 * 2171263 * 2
def baseEnd_2171263 : Nat := 1114901546323243657227049

theorem tailTrace_2171263 : CollatzResearch.WordTrace tailWord_2171263 prefixEnd_2171263 1114901546323243657227049 := by
  unfold tailWord_2171263
  simp only [CollatzResearch.WordTrace]
  refine ⟨79192467532892448042846443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52794978355261632028564295 79192467532892448042846443)
  ·
    refine ⟨118788701299338672064269665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79192467532892448042846443 118788701299338672064269665)
    ·
      refine ⟨89091525974504004048202249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118788701299338672064269665 89091525974504004048202249)
      ·
        refine ⟨66818644480878003036151687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89091525974504004048202249 66818644480878003036151687)
        ·
          refine ⟨100227966721317004554227531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66818644480878003036151687 100227966721317004554227531)
          ·
            refine ⟨150341950081975506831341297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100227966721317004554227531 150341950081975506831341297)
            ·
              refine ⟨112756462561481630123505973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150341950081975506831341297 112756462561481630123505973)
              ·
                refine ⟨10570918365138902824078685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 112756462561481630123505973 10570918365138902824078685)
                ·
                  refine ⟨3964094386927088559029507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10570918365138902824078685 3964094386927088559029507)
                  ·
                    refine ⟨5946141580390632838544261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3964094386927088559029507 5946141580390632838544261)
                    ·
                      refine ⟨1114901546323243657227049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5946141580390632838544261 1114901546323243657227049)
                      ·
                        rfl

theorem cell23_2171263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 4].length) (baseStart_2171263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2171263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2171263 prefixEnd_2171263 := by exact prefixLift 2171263
  have htrace : WordTrace (prefixWord ++ tailWord_2171263) baseStart_2171263 baseEnd_2171263 := by
    simpa [prefixWord, tailWord_2171263, baseEnd_2171263] using wordTrace_append hprefix tailTrace_2171263
  have hstable : (prefixWord ++ tailWord_2171263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171263).length < 2 ^ (prefixWord ++ tailWord_2171263).sum := by decide
  have hdescent : baseEnd_2171263 < baseStart_2171263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171273 : List Nat := [1, 2, 1, 1, 6, 1, 1, 1, 3, 6]
def baseStart_2171273 : Nat := 118140960795 + 2171273 * 2 ^ 59
def prefixEnd_2171273 : Nat := 4983230072969 + 3 ^ 40 * 2171273 * 2
def baseEnd_2171273 : Nat := 371635560376596206034001

theorem tailTrace_2171273 : CollatzResearch.WordTrace tailWord_2171273 prefixEnd_2171273 371635560376596206034001 := by
  unfold tailWord_2171273
  simp only [CollatzResearch.WordTrace]
  refine ⟨79192832262856219750710473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52795221508570813167140315 79192832262856219750710473)
  ·
    refine ⟨59394624197142164813032855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79192832262856219750710473 59394624197142164813032855)
    ·
      refine ⟨89091936295713247219549283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59394624197142164813032855 89091936295713247219549283)
      ·
        refine ⟨133637904443569870829323925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89091936295713247219549283 133637904443569870829323925)
        ·
          refine ⟨6264276770792337695124559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 133637904443569870829323925 6264276770792337695124559)
          ·
            refine ⟨9396415156188506542686839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6264276770792337695124559 9396415156188506542686839)
            ·
              refine ⟨14094622734282759814030259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9396415156188506542686839 14094622734282759814030259)
              ·
                refine ⟨21141934101424139721045389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14094622734282759814030259 21141934101424139721045389)
                ·
                  refine ⟨7928225288034052395392021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21141934101424139721045389 7928225288034052395392021)
                  ·
                    refine ⟨371635560376596206034001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7928225288034052395392021 371635560376596206034001)
                    ·
                      rfl

theorem cell23_2171273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 3, 6].length) (baseStart_2171273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2171273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2171273 prefixEnd_2171273 := by exact prefixLift 2171273
  have htrace : WordTrace (prefixWord ++ tailWord_2171273) baseStart_2171273 baseEnd_2171273 := by
    simpa [prefixWord, tailWord_2171273, baseEnd_2171273] using wordTrace_append hprefix tailTrace_2171273
  have hstable : (prefixWord ++ tailWord_2171273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171273).length < 2 ^ (prefixWord ++ tailWord_2171273).sum := by decide
  have hdescent : baseEnd_2171273 < baseStart_2171273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171300 : List Nat := [2, 3, 1, 2, 1, 1, 3, 2, 3, 2, 3]
def baseStart_2171300 : Nat := 118140960795 + 2171300 * 2 ^ 59
def prefixEnd_2171300 : Nat := 4983230072969 + 3 ^ 40 * 2171300 * 2
def baseEnd_2171300 : Nat := 1114920545107460012464379

theorem tailTrace_2171300 : CollatzResearch.WordTrace tailWord_2171300 prefixEnd_2171300 1114920545107460012464379 := by
  unfold tailWord_2171300
  simp only [CollatzResearch.WordTrace]
  refine ⟨39596908516879201680971677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52795878022505602241295569 39596908516879201680971677)
  ·
    refine ⟨14848840693829700630364379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39596908516879201680971677 14848840693829700630364379)
    ·
      refine ⟨22273261040744550945546569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14848840693829700630364379 22273261040744550945546569)
      ·
        refine ⟨16704945780558413209159927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22273261040744550945546569 16704945780558413209159927)
        ·
          refine ⟨25057418670837619813739891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16704945780558413209159927 25057418670837619813739891)
          ·
            refine ⟨37586128006256429720609837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25057418670837619813739891 37586128006256429720609837)
            ·
              refine ⟨14094798002346161145228689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37586128006256429720609837 14094798002346161145228689)
              ·
                refine ⟨10571098501759620858921517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14094798002346161145228689 10571098501759620858921517)
                ·
                  refine ⟨3964161938159857822095569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10571098501759620858921517 3964161938159857822095569)
                  ·
                    refine ⟨2973121453619893366571677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3964161938159857822095569 2973121453619893366571677)
                    ·
                      refine ⟨1114920545107460012464379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2973121453619893366571677 1114920545107460012464379)
                      ·
                        rfl

theorem cell23_2171300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_2171300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2171300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2171300 prefixEnd_2171300 := by exact prefixLift 2171300
  have htrace : WordTrace (prefixWord ++ tailWord_2171300) baseStart_2171300 baseEnd_2171300 := by
    simpa [prefixWord, tailWord_2171300, baseEnd_2171300] using wordTrace_append hprefix tailTrace_2171300
  have hstable : (prefixWord ++ tailWord_2171300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171300).length < 2 ^ (prefixWord ++ tailWord_2171300).sum := by decide
  have hdescent : baseEnd_2171300 < baseStart_2171300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171374 : List Nat := [4, 1, 2, 1, 2, 2, 1, 4, 1, 3, 2]
def baseStart_2171374 : Nat := 118140960795 + 2171374 * 2 ^ 59
def prefixEnd_2171374 : Nat := 4983230072969 + 3 ^ 40 * 2171374 * 2
def baseEnd_2171374 : Nat := 1114958542675892722939039

theorem tailTrace_2171374 : CollatzResearch.WordTrace tailWord_2171374 prefixEnd_2171374 1114958542675892722939039 := by
  unfold tailWord_2171374
  simp only [CollatzResearch.WordTrace]
  refine ⟨9899564504436289250017147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52797677356993542666758117 9899564504436289250017147)
  ·
    refine ⟨14849346756654433875025721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9899564504436289250017147 14849346756654433875025721)
    ·
      refine ⟨11137010067490825406269291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14849346756654433875025721 11137010067490825406269291)
      ·
        refine ⟨16705515101236238109403937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11137010067490825406269291 16705515101236238109403937)
        ·
          refine ⟨12529136325927178582052953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16705515101236238109403937 12529136325927178582052953)
          ·
            refine ⟨9396852244445383936539715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12529136325927178582052953 9396852244445383936539715)
            ·
              refine ⟨14095278366668075904809573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9396852244445383936539715 14095278366668075904809573)
              ·
                refine ⟨2642864693750264232151795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14095278366668075904809573 2642864693750264232151795)
                ·
                  refine ⟨3964297040625396348227693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2642864693750264232151795 3964297040625396348227693)
                  ·
                    refine ⟨1486611390234523630585385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3964297040625396348227693 1486611390234523630585385)
                    ·
                      refine ⟨1114958542675892722939039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1486611390234523630585385 1114958542675892722939039)
                      ·
                        rfl

theorem cell23_2171374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 4, 1, 3, 2].length) (baseStart_2171374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2171374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2171374 prefixEnd_2171374 := by exact prefixLift 2171374
  have htrace : WordTrace (prefixWord ++ tailWord_2171374) baseStart_2171374 baseEnd_2171374 := by
    simpa [prefixWord, tailWord_2171374, baseEnd_2171374] using wordTrace_append hprefix tailTrace_2171374
  have hstable : (prefixWord ++ tailWord_2171374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171374).length < 2 ^ (prefixWord ++ tailWord_2171374).sum := by decide
  have hdescent : baseEnd_2171374 < baseStart_2171374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171398 : List Nat := [6, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3]
def baseStart_2171398 : Nat := 118140960795 + 2171398 * 2 ^ 59
def prefixEnd_2171398 : Nat := 4983230072969 + 3 ^ 40 * 2171398 * 2
def baseEnd_2171398 : Nat := 1114970866211600629038929

theorem tailTrace_2171398 : CollatzResearch.WordTrace tailWord_2171398 prefixEnd_2171398 1114970866211600629038929 := by
  unfold tailWord_2171398
  simp only [CollatzResearch.WordTrace]
  refine ⟨2474918480856355190594089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 52798260924935577399340565 2474918480856355190594089)
  ·
    refine ⟨1856188860642266392945567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2474918480856355190594089 1856188860642266392945567)
    ·
      refine ⟨2784283290963399589418351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1856188860642266392945567 2784283290963399589418351)
      ·
        refine ⟨4176424936445099384127527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2784283290963399589418351 4176424936445099384127527)
        ·
          refine ⟨6264637404667649076191291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4176424936445099384127527 6264637404667649076191291)
          ·
            refine ⟨9396956107001473614286937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6264637404667649076191291 9396956107001473614286937)
            ·
              refine ⟨7047717080251105210715203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9396956107001473614286937 7047717080251105210715203)
              ·
                refine ⟨10571575620376657816072805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7047717080251105210715203 10571575620376657816072805)
                ·
                  refine ⟨1982170428820623340513651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10571575620376657816072805 1982170428820623340513651)
                  ·
                    refine ⟨2973255643230935010770477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1982170428820623340513651 2973255643230935010770477)
                    ·
                      refine ⟨1114970866211600629038929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2973255643230935010770477 1114970866211600629038929)
                      ·
                        rfl

theorem cell23_2171398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_2171398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2171398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2171398 prefixEnd_2171398 := by exact prefixLift 2171398
  have htrace : WordTrace (prefixWord ++ tailWord_2171398) baseStart_2171398 baseEnd_2171398 := by
    simpa [prefixWord, tailWord_2171398, baseEnd_2171398] using wordTrace_append hprefix tailTrace_2171398
  have hstable : (prefixWord ++ tailWord_2171398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171398).length < 2 ^ (prefixWord ++ tailWord_2171398).sum := by decide
  have hdescent : baseEnd_2171398 < baseStart_2171398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171404 : List Nat := [2, 2, 1, 2, 4, 1, 2, 1, 4, 2, 2]
def baseStart_2171404 : Nat := 118140960795 + 2171404 * 2 ^ 59
def prefixEnd_2171404 : Nat := 4983230072969 + 3 ^ 40 * 2171404 * 2
def baseEnd_2171404 : Nat := 1114973947095527605563901

theorem tailTrace_2171404 : CollatzResearch.WordTrace tailWord_2171404 prefixEnd_2171404 1114973947095527605563901 := by
  unfold tailWord_2171404
  simp only [CollatzResearch.WordTrace]
  refine ⟨39598805112690814561864633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52798406816921086082486177 39598805112690814561864633)
  ·
    refine ⟨29699103834518110921398475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39598805112690814561864633 29699103834518110921398475)
    ·
      refine ⟨44548655751777166382097713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29699103834518110921398475 44548655751777166382097713)
      ·
        refine ⟨33411491813832874786573285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44548655751777166382097713 33411491813832874786573285)
        ·
          refine ⟨6264654715093664022482491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33411491813832874786573285 6264654715093664022482491)
          ·
            refine ⟨9396982072640496033723737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6264654715093664022482491 9396982072640496033723737)
            ·
              refine ⟨7047736554480372025292803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9396982072640496033723737 7047736554480372025292803)
              ·
                refine ⟨10571604831720558037939205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7047736554480372025292803 10571604831720558037939205)
                ·
                  refine ⟨1982175905947604632113601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10571604831720558037939205 1982175905947604632113601)
                  ·
                    refine ⟨1486631929460703474085201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1982175905947604632113601 1486631929460703474085201)
                    ·
                      refine ⟨1114973947095527605563901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1486631929460703474085201 1114973947095527605563901)
                      ·
                        rfl

theorem cell23_2171404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 4, 2, 2].length) (baseStart_2171404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2171404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2171404 prefixEnd_2171404 := by exact prefixLift 2171404
  have htrace : WordTrace (prefixWord ++ tailWord_2171404) baseStart_2171404 baseEnd_2171404 := by
    simpa [prefixWord, tailWord_2171404, baseEnd_2171404] using wordTrace_append hprefix tailTrace_2171404
  have hstable : (prefixWord ++ tailWord_2171404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171404).length < 2 ^ (prefixWord ++ tailWord_2171404).sum := by decide
  have hdescent : baseEnd_2171404 < baseStart_2171404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171415 : List Nat := [1, 1, 3, 6, 2, 1, 2, 1, 2, 1, 3]
def baseStart_2171415 : Nat := 118140960795 + 2171415 * 2 ^ 59
def prefixEnd_2171415 : Nat := 4983230072969 + 3 ^ 40 * 2171415 * 2
def baseEnd_2171415 : Nat := 1114979595382727062526351

theorem tailTrace_2171415 : CollatzResearch.WordTrace tailWord_2171415 prefixEnd_2171415 1114979595382727062526351 := by
  unfold tailWord_2171415
  simp only [CollatzResearch.WordTrace]
  refine ⟨79198011428341778002379699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52798674285561185334919799 79198011428341778002379699)
  ·
    refine ⟨118797017142512667003569549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79198011428341778002379699 118797017142512667003569549)
    ·
      refine ⟨44548881428442250126338581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118797017142512667003569549 44548881428442250126338581)
      ·
        refine ⟨2088228816958230474672121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 44548881428442250126338581 2088228816958230474672121)
        ·
          refine ⟨1566171612718672856004091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2088228816958230474672121 1566171612718672856004091)
          ·
            refine ⟨2349257419078009284006137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1566171612718672856004091 2349257419078009284006137)
            ·
              refine ⟨1761943064308506963004603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2349257419078009284006137 1761943064308506963004603)
              ·
                refine ⟨2642914596462760444506905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1761943064308506963004603 2642914596462760444506905)
                ·
                  refine ⟨1982185947347070333380179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2642914596462760444506905 1982185947347070333380179)
                  ·
                    refine ⟨2973278921020605500070269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1982185947347070333380179 2973278921020605500070269)
                    ·
                      refine ⟨1114979595382727062526351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2973278921020605500070269 1114979595382727062526351)
                      ·
                        rfl

theorem cell23_2171415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_2171415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2171415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2171415 prefixEnd_2171415 := by exact prefixLift 2171415
  have htrace : WordTrace (prefixWord ++ tailWord_2171415) baseStart_2171415 baseEnd_2171415 := by
    simpa [prefixWord, tailWord_2171415, baseEnd_2171415] using wordTrace_append hprefix tailTrace_2171415
  have hstable : (prefixWord ++ tailWord_2171415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171415).length < 2 ^ (prefixWord ++ tailWord_2171415).sum := by decide
  have hdescent : baseEnd_2171415 < baseStart_2171415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171421 : List Nat := [1, 4, 2, 2, 1, 3, 1, 3, 2, 2, 2]
def baseStart_2171421 : Nat := 118140960795 + 2171421 * 2 ^ 59
def prefixEnd_2171421 : Nat := 4983230072969 + 3 ^ 40 * 2171421 * 2
def baseEnd_2171421 : Nat := 1114982676266654039051323

theorem tailTrace_2171421 : CollatzResearch.WordTrace tailWord_2171421 prefixEnd_2171421 1114982676266654039051323 := by
  unfold tailWord_2171421
  simp only [CollatzResearch.WordTrace]
  refine ⟨79198230266320041027098117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52798820177546694018065411 79198230266320041027098117)
  ·
    refine ⟨14849668174935007692580897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79198230266320041027098117 14849668174935007692580897)
    ·
      refine ⟨11137251131201255769435673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14849668174935007692580897 11137251131201255769435673)
      ·
        refine ⟨8352938348400941827076755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11137251131201255769435673 8352938348400941827076755)
        ·
          refine ⟨12529407522601412740615133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8352938348400941827076755 12529407522601412740615133)
          ·
            refine ⟨4698527820975529777730675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12529407522601412740615133 4698527820975529777730675)
            ·
              refine ⟨7047791731463294666596013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4698527820975529777730675 7047791731463294666596013)
              ·
                refine ⟨2642921899298735499973505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7047791731463294666596013 2642921899298735499973505)
                ·
                  refine ⟨1982191424474051624980129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2642921899298735499973505 1982191424474051624980129)
                  ·
                    refine ⟨1486643568355538718735097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1982191424474051624980129 1486643568355538718735097)
                    ·
                      refine ⟨1114982676266654039051323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1486643568355538718735097 1114982676266654039051323)
                      ·
                        rfl

theorem cell23_2171421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_2171421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2171421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2171421 prefixEnd_2171421 := by exact prefixLift 2171421
  have htrace : WordTrace (prefixWord ++ tailWord_2171421) baseStart_2171421 baseEnd_2171421 := by
    simpa [prefixWord, tailWord_2171421, baseEnd_2171421] using wordTrace_append hprefix tailTrace_2171421
  have hstable : (prefixWord ++ tailWord_2171421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171421).length < 2 ^ (prefixWord ++ tailWord_2171421).sum := by decide
  have hdescent : baseEnd_2171421 < baseStart_2171421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171440 : List Nat := [2, 1, 1, 1, 2, 3, 3, 3, 2, 5]
def baseStart_2171440 : Nat := 118140960795 + 2171440 * 2 ^ 59
def prefixEnd_2171440 : Nat := 4983230072969 + 3 ^ 40 * 2171440 * 2
def baseEnd_2171440 : Nat := 371664144133029821571245

theorem tailTrace_2171440 : CollatzResearch.WordTrace tailWord_2171440 prefixEnd_2171440 371664144133029821571245 := by
  unfold tailWord_2171440
  simp only [CollatzResearch.WordTrace]
  refine ⟨39599461626625603636019887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52799282168834138181359849 39599461626625603636019887)
  ·
    refine ⟨59399192439938405454029831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39599461626625603636019887 59399192439938405454029831)
    ·
      refine ⟨89098788659907608181044747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59399192439938405454029831 89098788659907608181044747)
      ·
        refine ⟨133648182989861412271567121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89098788659907608181044747 133648182989861412271567121)
        ·
          refine ⟨100236137242396059203675341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133648182989861412271567121 100236137242396059203675341)
          ·
            refine ⟨37588551465898522201378253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100236137242396059203675341 37588551465898522201378253)
            ·
              refine ⟨14095706799711945825516845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37588551465898522201378253 14095706799711945825516845)
              ·
                refine ⟨5285890049891979684568817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14095706799711945825516845 5285890049891979684568817)
                ·
                  refine ⟨3964417537418984763426613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5285890049891979684568817 3964417537418984763426613)
                  ·
                    refine ⟨371664144133029821571245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3964417537418984763426613 371664144133029821571245)
                    ·
                      rfl

theorem cell23_2171440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3, 2, 5].length) (baseStart_2171440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2171440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2171440 prefixEnd_2171440 := by exact prefixLift 2171440
  have htrace : WordTrace (prefixWord ++ tailWord_2171440) baseStart_2171440 baseEnd_2171440 := by
    simpa [prefixWord, tailWord_2171440, baseEnd_2171440] using wordTrace_append hprefix tailTrace_2171440
  have hstable : (prefixWord ++ tailWord_2171440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171440).length < 2 ^ (prefixWord ++ tailWord_2171440).sum := by decide
  have hdescent : baseEnd_2171440 < baseStart_2171440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171450 : List Nat := [3, 1, 1, 1, 3, 3, 1, 2, 1, 2, 5]
def baseStart_2171450 : Nat := 118140960795 + 2171450 * 2 ^ 59
def prefixEnd_2171450 : Nat := 4983230072969 + 3 ^ 40 * 2171450 * 2
def baseEnd_2171450 : Nat := 1114997567205634425588689

theorem tailTrace_2171450 : CollatzResearch.WordTrace tailWord_2171450 prefixEnd_2171450 1114997567205634425588689 := by
  unfold tailWord_2171450
  simp only [CollatzResearch.WordTrace]
  refine ⟨19799821995803744744975951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52799525322143319319935869 19799821995803744744975951)
  ·
    refine ⟨29699732993705617117463927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19799821995803744744975951 29699732993705617117463927)
    ·
      refine ⟨44549599490558425676195891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29699732993705617117463927 44549599490558425676195891)
      ·
        refine ⟨66824399235837638514293837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44549599490558425676195891 66824399235837638514293837)
        ·
          refine ⟨25059149713439114442860189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66824399235837638514293837 25059149713439114442860189)
          ·
            refine ⟨9397181142539667916072571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25059149713439114442860189 9397181142539667916072571)
            ·
              refine ⟨14095771713809501874108857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9397181142539667916072571 14095771713809501874108857)
              ·
                refine ⟨10571828785357126405581643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14095771713809501874108857 10571828785357126405581643)
                ·
                  refine ⟨15857743178035689608372465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10571828785357126405581643 15857743178035689608372465)
                  ·
                    refine ⟨11893307383526767206279349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15857743178035689608372465 11893307383526767206279349)
                    ·
                      refine ⟨1114997567205634425588689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11893307383526767206279349 1114997567205634425588689)
                      ·
                        rfl

theorem cell23_2171450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 1, 2, 5].length) (baseStart_2171450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2171450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2171450 prefixEnd_2171450 := by exact prefixLift 2171450
  have htrace : WordTrace (prefixWord ++ tailWord_2171450) baseStart_2171450 baseEnd_2171450 := by
    simpa [prefixWord, tailWord_2171450, baseEnd_2171450] using wordTrace_append hprefix tailTrace_2171450
  have hstable : (prefixWord ++ tailWord_2171450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171450).length < 2 ^ (prefixWord ++ tailWord_2171450).sum := by decide
  have hdescent : baseEnd_2171450 < baseStart_2171450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171457 : List Nat := [1, 2, 5, 1, 1, 2, 2, 2, 2, 5]
def baseStart_2171457 : Nat := 118140960795 + 2171457 * 2 ^ 59
def prefixEnd_2171457 : Nat := 4983230072969 + 3 ^ 40 * 2171457 * 2
def baseEnd_2171457 : Nat := 371667053856738632733719

theorem tailTrace_2171457 : CollatzResearch.WordTrace tailWord_2171457 prefixEnd_2171457 371667053856738632733719 := by
  unfold tailWord_2171457
  simp only [CollatzResearch.WordTrace]
  refine ⟨79199543294189619175408625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52799695529459746116939083 79199543294189619175408625)
  ·
    refine ⟨59399657470642214381556469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79199543294189619175408625 59399657470642214381556469)
    ·
      refine ⟨5568717887872707598270919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59399657470642214381556469 5568717887872707598270919)
      ·
        refine ⟨8353076831809061397406379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5568717887872707598270919 8353076831809061397406379)
        ·
          refine ⟨12529615247713592096109569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8353076831809061397406379 12529615247713592096109569)
          ·
            refine ⟨9397211435785194072082177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12529615247713592096109569 9397211435785194072082177)
            ·
              refine ⟨7047908576838895554061633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9397211435785194072082177 7047908576838895554061633)
              ·
                refine ⟨5285931432629171665546225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7047908576838895554061633 5285931432629171665546225)
                ·
                  refine ⟨3964448574471878749159669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5285931432629171665546225 3964448574471878749159669)
                  ·
                    refine ⟨371667053856738632733719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3964448574471878749159669 371667053856738632733719)
                    ·
                      rfl

theorem cell23_2171457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_2171457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2171457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2171457 prefixEnd_2171457 := by exact prefixLift 2171457
  have htrace : WordTrace (prefixWord ++ tailWord_2171457) baseStart_2171457 baseEnd_2171457 := by
    simpa [prefixWord, tailWord_2171457, baseEnd_2171457] using wordTrace_append hprefix tailTrace_2171457
  have hstable : (prefixWord ++ tailWord_2171457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171457).length < 2 ^ (prefixWord ++ tailWord_2171457).sum := by decide
  have hdescent : baseEnd_2171457 < baseStart_2171457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171477 : List Nat := [1, 3, 2, 2, 1, 1, 3, 1, 1, 6, 2]
def baseStart_2171477 : Nat := 118140960795 + 2171477 * 2 ^ 59
def prefixEnd_2171477 : Nat := 4983230072969 + 3 ^ 40 * 2171477 * 2
def baseEnd_2171477 : Nat := 1115011431183305819951065

theorem tailTrace_2171477 : CollatzResearch.WordTrace tailWord_2171477 prefixEnd_2171477 1115011431183305819951065 := by
  unfold tailWord_2171477
  simp only [CollatzResearch.WordTrace]
  refine ⟨79200272754117162591136685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52800181836078108394091123 79200272754117162591136685)
  ·
    refine ⟨29700102282793935971676257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79200272754117162591136685 29700102282793935971676257)
    ·
      refine ⟨22275076712095451978757193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29700102282793935971676257 22275076712095451978757193)
      ·
        refine ⟨16706307534071588984067895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22275076712095451978757193 16706307534071588984067895)
        ·
          refine ⟨25059461301107383476101843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16706307534071588984067895 25059461301107383476101843)
          ·
            refine ⟨37589191951661075214152765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25059461301107383476101843 37589191951661075214152765)
            ·
              refine ⟨14095946981872903205307287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37589191951661075214152765 14095946981872903205307287)
              ·
                refine ⟨21143920472809354807960931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14095946981872903205307287 21143920472809354807960931)
                ·
                  refine ⟨31715880709214032211941397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21143920472809354807960931 31715880709214032211941397)
                  ·
                    refine ⟨1486681908244407759934753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 31715880709214032211941397 1486681908244407759934753)
                    ·
                      refine ⟨1115011431183305819951065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1486681908244407759934753 1115011431183305819951065)
                      ·
                        rfl

theorem cell23_2171477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 6, 2].length) (baseStart_2171477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2171477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2171477 prefixEnd_2171477 := by exact prefixLift 2171477
  have htrace : WordTrace (prefixWord ++ tailWord_2171477) baseStart_2171477 baseEnd_2171477 := by
    simpa [prefixWord, tailWord_2171477, baseEnd_2171477] using wordTrace_append hprefix tailTrace_2171477
  have hstable : (prefixWord ++ tailWord_2171477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171477).length < 2 ^ (prefixWord ++ tailWord_2171477).sum := by decide
  have hdescent : baseEnd_2171477 < baseStart_2171477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171517 : List Nat := [1, 4, 1, 1, 5, 1, 1, 1, 8]
def baseStart_2171517 : Nat := 118140960795 + 2171517 * 2 ^ 59
def prefixEnd_2171517 : Nat := 4983230072969 + 3 ^ 40 * 2171517 * 2
def baseEnd_2171517 : Nat := 123892441156609518161209

theorem tailTrace_2171517 : CollatzResearch.WordTrace tailWord_2171517 prefixEnd_2171517 123892441156609518161209 := by
  unfold tailWord_2171517
  simp only [CollatzResearch.WordTrace]
  refine ⟨79201731673972249422592805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52801154449314832948395203 79201731673972249422592805)
  ·
    refine ⟨14850324688869796766736151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79201731673972249422592805 14850324688869796766736151)
    ·
      refine ⟨22275487033304695150104227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14850324688869796766736151 22275487033304695150104227)
      ·
        refine ⟨33413230549957042725156341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22275487033304695150104227 33413230549957042725156341)
        ·
          refine ⟨3132490364058472755483407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33413230549957042725156341 3132490364058472755483407)
          ·
            refine ⟨4698735546087709133225111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3132490364058472755483407 4698735546087709133225111)
            ·
              refine ⟨7048103319131563699837667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4698735546087709133225111 7048103319131563699837667)
              ·
                refine ⟨10572154978697345549756501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7048103319131563699837667 10572154978697345549756501)
                ·
                  refine ⟨123892441156609518161209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10572154978697345549756501 123892441156609518161209)
                  ·
                    rfl

theorem cell23_2171517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 8].length) (baseStart_2171517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2171517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2171517 prefixEnd_2171517 := by exact prefixLift 2171517
  have htrace : WordTrace (prefixWord ++ tailWord_2171517) baseStart_2171517 baseEnd_2171517 := by
    simpa [prefixWord, tailWord_2171517, baseEnd_2171517] using wordTrace_append hprefix tailTrace_2171517
  have hstable : (prefixWord ++ tailWord_2171517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171517).length < 2 ^ (prefixWord ++ tailWord_2171517).sum := by decide
  have hdescent : baseEnd_2171517 < baseStart_2171517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171520 : List Nat := [2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 6]
def baseStart_2171520 : Nat := 118140960795 + 2171520 * 2 ^ 59
def prefixEnd_2171520 : Nat := 4983230072969 + 3 ^ 40 * 2171520 * 2
def baseEnd_2171520 : Nat := 1115033510851449151713367

theorem tailTrace_2171520 : CollatzResearch.WordTrace tailWord_2171520 prefixEnd_2171520 1115033510851449151713367 := by
  unfold tailWord_2171520
  simp only [CollatzResearch.WordTrace]
  refine ⟨39600920546480690467476007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52801227395307587289968009 39600920546480690467476007)
  ·
    refine ⟨59401380819721035701214011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39600920546480690467476007 59401380819721035701214011)
    ·
      refine ⟨89102071229581553551821017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59401380819721035701214011 89102071229581553551821017)
      ·
        refine ⟨66826553422186165163865763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89102071229581553551821017 66826553422186165163865763)
        ·
          refine ⟨100239830133279247745798645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66826553422186165163865763 100239830133279247745798645)
          ·
            refine ⟨9397484074994929476168623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 100239830133279247745798645 9397484074994929476168623)
            ·
              refine ⟨14096226112492394214252935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9397484074994929476168623 14096226112492394214252935)
              ·
                refine ⟨21144339168738591321379403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14096226112492394214252935 21144339168738591321379403)
                ·
                  refine ⟨31716508753107886982069105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21144339168738591321379403 31716508753107886982069105)
                  ·
                    refine ⟨23787381564830915236551829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31716508753107886982069105 23787381564830915236551829)
                    ·
                      refine ⟨1115033510851449151713367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23787381564830915236551829 1115033510851449151713367)
                      ·
                        rfl

theorem cell23_2171520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 6].length) (baseStart_2171520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2171520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2171520 prefixEnd_2171520 := by exact prefixLift 2171520
  have htrace : WordTrace (prefixWord ++ tailWord_2171520) baseStart_2171520 baseEnd_2171520 := by
    simpa [prefixWord, tailWord_2171520, baseEnd_2171520] using wordTrace_append hprefix tailTrace_2171520
  have hstable : (prefixWord ++ tailWord_2171520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171520).length < 2 ^ (prefixWord ++ tailWord_2171520).sum := by decide
  have hdescent : baseEnd_2171520 < baseStart_2171520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171534 : List Nat := [4, 1, 1, 3, 1, 1, 5, 1, 6]
def baseStart_2171534 : Nat := 118140960795 + 2171534 * 2 ^ 59
def prefixEnd_2171534 : Nat := 4983230072969 + 3 ^ 40 * 2171534 * 2
def baseEnd_2171534 : Nat := 123893411064512455215367

theorem tailTrace_2171534 : CollatzResearch.WordTrace tailWord_2171534 prefixEnd_2171534 123893411064512455215367 := by
  unfold tailWord_2171534
  simp only [CollatzResearch.WordTrace]
  refine ⟨9900293964363832665745207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52801567809940440883974437 9900293964363832665745207)
  ·
    refine ⟨14850440946545748998617811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9900293964363832665745207 14850440946545748998617811)
    ·
      refine ⟨22275661419818623497926717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14850440946545748998617811 22275661419818623497926717)
      ·
        refine ⟨8353373032431983811722519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22275661419818623497926717 8353373032431983811722519)
        ·
          refine ⟨12530059548647975717583779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8353373032431983811722519 12530059548647975717583779)
          ·
            refine ⟨18795089322971963576375669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12530059548647975717583779 18795089322971963576375669)
            ·
              refine ⟨1762039624028621585285219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18795089322971963576375669 1762039624028621585285219)
              ·
                refine ⟨2643059436042932377927829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1762039624028621585285219 2643059436042932377927829)
                ·
                  refine ⟨123893411064512455215367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2643059436042932377927829 123893411064512455215367)
                  ·
                    rfl

theorem cell23_2171534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 1, 6].length) (baseStart_2171534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2171534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2171534 prefixEnd_2171534 := by exact prefixLift 2171534
  have htrace : WordTrace (prefixWord ++ tailWord_2171534) baseStart_2171534 baseEnd_2171534 := by
    simpa [prefixWord, tailWord_2171534, baseEnd_2171534] using wordTrace_append hprefix tailTrace_2171534
  have hstable : (prefixWord ++ tailWord_2171534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171534).length < 2 ^ (prefixWord ++ tailWord_2171534).sum := by decide
  have hdescent : baseEnd_2171534 < baseStart_2171534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171544 : List Nat := [2, 1, 2, 4, 1, 1, 1, 4, 3, 1, 3]
def baseStart_2171544 : Nat := 118140960795 + 2171544 * 2 ^ 59
def prefixEnd_2171544 : Nat := 4983230072969 + 3 ^ 40 * 2171544 * 2
def baseEnd_2171544 : Nat := 1115045834387157057813257

theorem tailTrace_2171544 : CollatzResearch.WordTrace tailWord_2171544 prefixEnd_2171544 1115045834387157057813257 := by
  unfold tailWord_2171544
  simp only [CollatzResearch.WordTrace]
  refine ⟨39601358222437216516912843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52801810963249622022550457 39601358222437216516912843)
  ·
    refine ⟨59402037333655824775369265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39601358222437216516912843 59402037333655824775369265)
    ·
      refine ⟨44551528000241868581526949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59402037333655824775369265 44551528000241868581526949)
      ·
        refine ⟨8353411500045350359036303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44551528000241868581526949 8353411500045350359036303)
        ·
          refine ⟨12530117250068025538554455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8353411500045350359036303 12530117250068025538554455)
          ·
            refine ⟨18795175875102038307831683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12530117250068025538554455 18795175875102038307831683)
            ·
              refine ⟨28192763812653057461747525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18795175875102038307831683 28192763812653057461747525)
              ·
                refine ⟨5286143214872448274077661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28192763812653057461747525 5286143214872448274077661)
                ·
                  refine ⟨1982303705577168102779123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5286143214872448274077661 1982303705577168102779123)
                  ·
                    refine ⟨2973455558365752154168685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1982303705577168102779123 2973455558365752154168685)
                    ·
                      refine ⟨1115045834387157057813257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2973455558365752154168685 1115045834387157057813257)
                      ·
                        rfl

theorem cell23_2171544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_2171544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2171544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2171544 prefixEnd_2171544 := by exact prefixLift 2171544
  have htrace : WordTrace (prefixWord ++ tailWord_2171544) baseStart_2171544 baseEnd_2171544 := by
    simpa [prefixWord, tailWord_2171544, baseEnd_2171544] using wordTrace_append hprefix tailTrace_2171544
  have hstable : (prefixWord ++ tailWord_2171544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171544).length < 2 ^ (prefixWord ++ tailWord_2171544).sum := by decide
  have hdescent : baseEnd_2171544 < baseStart_2171544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171578 : List Nat := [3, 1, 1, 1, 2, 3, 5, 2, 1, 1, 3]
def baseStart_2171578 : Nat := 118140960795 + 2171578 * 2 ^ 59
def prefixEnd_2171578 : Nat := 4983230072969 + 3 ^ 40 * 2171578 * 2
def baseEnd_2171578 : Nat := 1115063292729409924788101

theorem tailTrace_2171578 : CollatzResearch.WordTrace tailWord_2171578 prefixEnd_2171578 1115063292729409924788101 := by
  unfold tailWord_2171578
  simp only [CollatzResearch.WordTrace]
  refine ⟨19800989131687814210140847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52802637684500837893708925 19800989131687814210140847)
  ·
    refine ⟨29701483697531721315211271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19800989131687814210140847 29701483697531721315211271)
    ·
      refine ⟨44552225546297581972816907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29701483697531721315211271 44552225546297581972816907)
      ·
        refine ⟨66828338319446372959225361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44552225546297581972816907 66828338319446372959225361)
        ·
          refine ⟨50121253739584779719419021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66828338319446372959225361 50121253739584779719419021)
          ·
            refine ⟨18795470152344292394782133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50121253739584779719419021 18795470152344292394782133)
            ·
              refine ⟨1762075326782277412010825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18795470152344292394782133 1762075326782277412010825)
              ·
                refine ⟨1321556495086708059008119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1762075326782277412010825 1321556495086708059008119)
                ·
                  refine ⟨1982334742630062088512179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1321556495086708059008119 1982334742630062088512179)
                  ·
                    refine ⟨2973502113945093132768269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1982334742630062088512179 2973502113945093132768269)
                    ·
                      refine ⟨1115063292729409924788101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2973502113945093132768269 1115063292729409924788101)
                      ·
                        rfl

theorem cell23_2171578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 2, 1, 1, 3].length) (baseStart_2171578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2171578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2171578 prefixEnd_2171578 := by exact prefixLift 2171578
  have htrace : WordTrace (prefixWord ++ tailWord_2171578) baseStart_2171578 baseEnd_2171578 := by
    simpa [prefixWord, tailWord_2171578, baseEnd_2171578] using wordTrace_append hprefix tailTrace_2171578
  have hstable : (prefixWord ++ tailWord_2171578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171578).length < 2 ^ (prefixWord ++ tailWord_2171578).sum := by decide
  have hdescent : baseEnd_2171578 < baseStart_2171578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171585 : List Nat := [1, 2, 6, 2, 2, 1, 2, 1, 6]
def baseStart_2171585 : Nat := 118140960795 + 2171585 * 2 ^ 59
def prefixEnd_2171585 : Nat := 4983230072969 + 3 ^ 40 * 2171585 * 2
def baseEnd_2171585 : Nat := 123896320788221266377841

theorem tailTrace_2171585 : CollatzResearch.WordTrace tailWord_2171585 prefixEnd_2171585 123896320788221266377841 := by
  unfold tailWord_2171585
  simp only [CollatzResearch.WordTrace]
  refine ⟨79204211837725897036068209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52802807891817264690712139 79204211837725897036068209)
  ·
    refine ⟨59403158878294422777051157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79204211837725897036068209 59403158878294422777051157)
    ·
      refine ⟨2784523072420051067674273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 59403158878294422777051157 2784523072420051067674273)
      ·
        refine ⟨2088392304315038300755705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2784523072420051067674273 2088392304315038300755705)
        ·
          refine ⟨1566294228236278725566779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2088392304315038300755705 1566294228236278725566779)
          ·
            refine ⟨2349441342354418088350169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1566294228236278725566779 2349441342354418088350169)
            ·
              refine ⟨1762081006765813566262627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2349441342354418088350169 1762081006765813566262627)
              ·
                refine ⟨2643121510148720349393941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1762081006765813566262627 2643121510148720349393941)
                ·
                  refine ⟨123896320788221266377841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2643121510148720349393941 123896320788221266377841)
                  ·
                    rfl

theorem cell23_2171585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 1, 6].length) (baseStart_2171585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2171585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2171585 prefixEnd_2171585 := by exact prefixLift 2171585
  have htrace : WordTrace (prefixWord ++ tailWord_2171585) baseStart_2171585 baseEnd_2171585 := by
    simpa [prefixWord, tailWord_2171585, baseEnd_2171585] using wordTrace_append hprefix tailTrace_2171585
  have hstable : (prefixWord ++ tailWord_2171585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171585).length < 2 ^ (prefixWord ++ tailWord_2171585).sum := by decide
  have hdescent : baseEnd_2171585 < baseStart_2171585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171702 : List Nat := [5, 1, 2, 2, 2, 1, 3, 1, 2, 1, 3]
def baseStart_2171702 : Nat := 118140960795 + 2171702 * 2 ^ 59
def prefixEnd_2171702 : Nat := 4983230072969 + 3 ^ 40 * 2171702 * 2
def baseEnd_2171702 : Nat := 1115126964330567439637531

theorem tailTrace_2171702 : CollatzResearch.WordTrace tailWord_2171702 prefixEnd_2171702 1115126964330567439637531 := by
  unfold tailWord_2171702
  simp only [CollatzResearch.WordTrace]
  refine ⟨4950529948643876626129835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52805652785534684012051573 4950529948643876626129835)
  ·
    refine ⟨7425794922965814939194753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4950529948643876626129835 7425794922965814939194753)
    ·
      refine ⟨5569346192224361204396065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7425794922965814939194753 5569346192224361204396065)
      ·
        refine ⟨4177009644168270903297049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5569346192224361204396065 4177009644168270903297049)
        ·
          refine ⟨3132757233126203177472787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4177009644168270903297049 3132757233126203177472787)
          ·
            refine ⟨4699135849689304766209181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3132757233126203177472787 4699135849689304766209181)
            ·
              refine ⟨1762175943633489287328443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4699135849689304766209181 1762175943633489287328443)
              ·
                refine ⟨2643263915450233930992665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1762175943633489287328443 2643263915450233930992665)
                ·
                  refine ⟨1982447936587675448244499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2643263915450233930992665 1982447936587675448244499)
                  ·
                    refine ⟨2973671904881513172366749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1982447936587675448244499 2973671904881513172366749)
                    ·
                      refine ⟨1115126964330567439637531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2973671904881513172366749 1115126964330567439637531)
                      ·
                        rfl

theorem cell23_2171702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_2171702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2171702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2171702 prefixEnd_2171702 := by exact prefixLift 2171702
  have htrace : WordTrace (prefixWord ++ tailWord_2171702) baseStart_2171702 baseEnd_2171702 := by
    simpa [prefixWord, tailWord_2171702, baseEnd_2171702] using wordTrace_append hprefix tailTrace_2171702
  have hstable : (prefixWord ++ tailWord_2171702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171702).length < 2 ^ (prefixWord ++ tailWord_2171702).sum := by decide
  have hdescent : baseEnd_2171702 < baseStart_2171702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171727 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 8, 5]
def baseStart_2171727 : Nat := 118140960795 + 2171727 * 2 ^ 59
def prefixEnd_2171727 : Nat := 4983230072969 + 3 ^ 40 * 2171727 * 2
def baseEnd_2171727 : Nat := 371713267115643280608305

theorem tailTrace_2171727 : CollatzResearch.WordTrace tailWord_2171727 prefixEnd_2171727 371713267115643280608305 := by
  unfold tailWord_2171727
  simp only [CollatzResearch.WordTrace]
  refine ⟨79209391003211455287737435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52806260668807636858491623 79209391003211455287737435)
  ·
    refine ⟨118814086504817182931606153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79209391003211455287737435 118814086504817182931606153)
    ·
      refine ⟨89110564878612887198704615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118814086504817182931606153 89110564878612887198704615)
      ·
        refine ⟨133665847317919330798056923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89110564878612887198704615 133665847317919330798056923)
        ·
          refine ⟨200498770976878996197085385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133665847317919330798056923 200498770976878996197085385)
          ·
            refine ⟨150374078232659247147814039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200498770976878996197085385 150374078232659247147814039)
            ·
              refine ⟨225561117348988870721721059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150374078232659247147814039 225561117348988870721721059)
              ·
                refine ⟨338341676023483306082581589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 225561117348988870721721059 338341676023483306082581589)
                ·
                  refine ⟨3964941515900194993155253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 338341676023483306082581589 3964941515900194993155253)
                  ·
                    refine ⟨371713267115643280608305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3964941515900194993155253 371713267115643280608305)
                    ·
                      rfl

theorem cell23_2171727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 8, 5].length) (baseStart_2171727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2171727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2171727 prefixEnd_2171727 := by exact prefixLift 2171727
  have htrace : WordTrace (prefixWord ++ tailWord_2171727) baseStart_2171727 baseEnd_2171727 := by
    simpa [prefixWord, tailWord_2171727, baseEnd_2171727] using wordTrace_append hprefix tailTrace_2171727
  have hstable : (prefixWord ++ tailWord_2171727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171727).length < 2 ^ (prefixWord ++ tailWord_2171727).sum := by decide
  have hdescent : baseEnd_2171727 < baseStart_2171727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171744 : List Nat := [2, 1, 1, 3, 3, 1, 3, 2, 2, 5]
def baseStart_2171744 : Nat := 118140960795 + 2171744 * 2 ^ 59
def prefixEnd_2171744 : Nat := 4983230072969 + 3 ^ 40 * 2171744 * 2
def baseEnd_2171744 : Nat := 371716176839352091770779

theorem tailTrace_2171744 : CollatzResearch.WordTrace tailWord_2171744 prefixEnd_2171744 371716176839352091770779 := by
  unfold tailWord_2171744
  simp only [CollatzResearch.WordTrace]
  refine ⟨39605005522074933595553143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52806674029433244794070857 39605005522074933595553143)
  ·
    refine ⟨59407508283112400393329715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39605005522074933595553143 59407508283112400393329715)
    ·
      refine ⟨89111262424668600589994573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59407508283112400393329715 89111262424668600589994573)
      ·
        refine ⟨33416723409250725221247965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89111262424668600589994573 33416723409250725221247965)
        ·
          refine ⟨12531271278469021957967987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33416723409250725221247965 12531271278469021957967987)
          ·
            refine ⟨18796906917703532936951981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12531271278469021957967987 18796906917703532936951981)
            ·
              refine ⟨7048840094138824851356993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18796906917703532936951981 7048840094138824851356993)
              ·
                refine ⟨5286630070604118638517745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7048840094138824851356993 5286630070604118638517745)
                ·
                  refine ⟨3964972552953088978888309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5286630070604118638517745 3964972552953088978888309)
                  ·
                    refine ⟨371716176839352091770779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3964972552953088978888309 371716176839352091770779)
                    ·
                      rfl

theorem cell23_2171744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2, 2, 5].length) (baseStart_2171744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2171744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2171744 prefixEnd_2171744 := by exact prefixLift 2171744
  have htrace : WordTrace (prefixWord ++ tailWord_2171744) baseStart_2171744 baseEnd_2171744 := by
    simpa [prefixWord, tailWord_2171744, baseEnd_2171744] using wordTrace_append hprefix tailTrace_2171744
  have hstable : (prefixWord ++ tailWord_2171744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171744).length < 2 ^ (prefixWord ++ tailWord_2171744).sum := by decide
  have hdescent : baseEnd_2171744 < baseStart_2171744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171748 : List Nat := [2, 3, 1, 1, 4, 2, 3, 2, 5]
def baseStart_2171748 : Nat := 118140960795 + 2171748 * 2 ^ 59
def prefixEnd_2171748 : Nat := 4983230072969 + 3 ^ 40 * 2171748 * 2
def baseEnd_2171748 : Nat := 123905620493408251073591

theorem tailTrace_2171748 : CollatzResearch.WordTrace tailWord_2171748 prefixEnd_2171748 123905620493408251073591 := by
  unfold tailWord_2171748
  simp only [CollatzResearch.WordTrace]
  refine ⟨39605078468067687937125949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52806771290756917249501265 39605078468067687937125949)
  ·
    refine ⟨14851904425525382976422231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39605078468067687937125949 14851904425525382976422231)
    ·
      refine ⟨22277856638288074464633347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14851904425525382976422231 22277856638288074464633347)
      ·
        refine ⟨33416784957432111696950021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22277856638288074464633347 33416784957432111696950021)
        ·
          refine ⟨6265647179518520943178129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33416784957432111696950021 6265647179518520943178129)
          ·
            refine ⟨4699235384638890707383597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6265647179518520943178129 4699235384638890707383597)
            ·
              refine ⟨1762213269239584015268849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4699235384638890707383597 1762213269239584015268849)
              ·
                refine ⟨1321659951929688011451637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1762213269239584015268849 1321659951929688011451637)
                ·
                  refine ⟨123905620493408251073591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1321659951929688011451637 123905620493408251073591)
                  ·
                    rfl

theorem cell23_2171748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 2, 5].length) (baseStart_2171748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2171748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2171748 prefixEnd_2171748 := by exact prefixLift 2171748
  have htrace : WordTrace (prefixWord ++ tailWord_2171748) baseStart_2171748 baseEnd_2171748 := by
    simpa [prefixWord, tailWord_2171748, baseEnd_2171748] using wordTrace_append hprefix tailTrace_2171748
  have hstable : (prefixWord ++ tailWord_2171748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171748).length < 2 ^ (prefixWord ++ tailWord_2171748).sum := by decide
  have hdescent : baseEnd_2171748 < baseStart_2171748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171767 : List Nat := [1, 1, 3, 1, 1, 2, 1, 2, 1, 5, 5]
def baseStart_2171767 : Nat := 118140960795 + 2171767 * 2 ^ 59
def prefixEnd_2171767 : Nat := 4983230072969 + 3 ^ 40 * 2171767 * 2
def baseEnd_2171767 : Nat := 1115160340573109685324731

theorem tailTrace_2171767 : CollatzResearch.WordTrace tailWord_2171767 prefixEnd_2171767 1115160340573109685324731 := by
  unfold tailWord_2171767
  simp only [CollatzResearch.WordTrace]
  refine ⟨79210849923066542119193555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52807233282044361412795703 79210849923066542119193555)
  ·
    refine ⟨118816274884599813178790333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79210849923066542119193555 118816274884599813178790333)
    ·
      refine ⟨44556103081724929942046375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118816274884599813178790333 44556103081724929942046375)
      ·
        refine ⟨66834154622587394913069563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44556103081724929942046375 66834154622587394913069563)
        ·
          refine ⟨100251231933881092369604345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66834154622587394913069563 100251231933881092369604345)
          ·
            refine ⟨75188423950410819277203259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100251231933881092369604345 75188423950410819277203259)
            ·
              refine ⟨112782635925616228915804889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75188423950410819277203259 112782635925616228915804889)
              ·
                refine ⟨84586976944212171686853667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112782635925616228915804889 84586976944212171686853667)
                ·
                  refine ⟨126880465416318257530280501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84586976944212171686853667 126880465416318257530280501)
                  ·
                    refine ⟨11895043632779836643463797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 126880465416318257530280501 11895043632779836643463797)
                    ·
                      refine ⟨1115160340573109685324731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11895043632779836643463797 1115160340573109685324731)
                      ·
                        rfl

theorem cell23_2171767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5, 5].length) (baseStart_2171767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2171767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2171767 prefixEnd_2171767 := by exact prefixLift 2171767
  have htrace : WordTrace (prefixWord ++ tailWord_2171767) baseStart_2171767 baseEnd_2171767 := by
    simpa [prefixWord, tailWord_2171767, baseEnd_2171767] using wordTrace_append hprefix tailTrace_2171767
  have hstable : (prefixWord ++ tailWord_2171767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171767).length < 2 ^ (prefixWord ++ tailWord_2171767).sum := by decide
  have hdescent : baseEnd_2171767 < baseStart_2171767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171781 : List Nat := [1, 3, 1, 1, 3, 4, 2, 1, 2, 1, 4]
def baseStart_2171781 : Nat := 118140960795 + 2171781 * 2 ^ 59
def prefixEnd_2171781 : Nat := 4983230072969 + 3 ^ 40 * 2171781 * 2
def baseEnd_2171781 : Nat := 1115167529302272630549667

theorem tailTrace_2171781 : CollatzResearch.WordTrace tailWord_2171781 prefixEnd_2171781 1115167529302272630549667 := by
  unfold tailWord_2171781
  simp only [CollatzResearch.WordTrace]
  refine ⟨79211360545015822510203197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52807573696677215006802131 79211360545015822510203197)
  ·
    refine ⟨29704260204380933441326199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79211360545015822510203197 29704260204380933441326199)
    ·
      refine ⟨44556390306571400161989299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29704260204380933441326199 44556390306571400161989299)
      ·
        refine ⟨66834585459857100242983949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44556390306571400161989299 66834585459857100242983949)
        ·
          refine ⟨25062969547446412591118981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66834585459857100242983949 25062969547446412591118981)
          ·
            refine ⟨4699306790146202360834809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25062969547446412591118981 4699306790146202360834809)
            ·
              refine ⟨3524480092609651770626107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4699306790146202360834809 3524480092609651770626107)
              ·
                refine ⟨5286720138914477655939161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3524480092609651770626107 5286720138914477655939161)
                ·
                  refine ⟨3965040104185858241954371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5286720138914477655939161 3965040104185858241954371)
                  ·
                    refine ⟨5947560156278787362931557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3965040104185858241954371 5947560156278787362931557)
                    ·
                      refine ⟨1115167529302272630549667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5947560156278787362931557 1115167529302272630549667)
                      ·
                        rfl

theorem cell23_2171781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 1, 2, 1, 4].length) (baseStart_2171781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2171781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2171781 prefixEnd_2171781 := by exact prefixLift 2171781
  have htrace : WordTrace (prefixWord ++ tailWord_2171781) baseStart_2171781 baseEnd_2171781 := by
    simpa [prefixWord, tailWord_2171781, baseEnd_2171781] using wordTrace_append hprefix tailTrace_2171781
  have hstable : (prefixWord ++ tailWord_2171781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171781).length < 2 ^ (prefixWord ++ tailWord_2171781).sum := by decide
  have hdescent : baseEnd_2171781 < baseStart_2171781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171787 : List Nat := [1, 1, 1, 1, 4, 2, 2, 1, 10]
def baseStart_2171787 : Nat := 118140960795 + 2171787 * 2 ^ 59
def prefixEnd_2171787 : Nat := 4983230072969 + 3 ^ 40 * 2171787 * 2
def baseEnd_2171787 : Nat := 123907845576244400786071

theorem tailTrace_2171787 : CollatzResearch.WordTrace tailWord_2171787 prefixEnd_2171787 123907845576244400786071 := by
  unfold tailWord_2171787
  simp only [CollatzResearch.WordTrace]
  refine ⟨79211579382994085534921615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52807719588662723689947743 79211579382994085534921615)
  ·
    refine ⟨118817369074491128302382423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79211579382994085534921615 118817369074491128302382423)
    ·
      refine ⟨178226053611736692453573635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118817369074491128302382423 178226053611736692453573635)
      ·
        refine ⟨267339080417605038680360453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178226053611736692453573635 267339080417605038680360453)
        ·
          refine ⟨50126077578300944752567585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 267339080417605038680360453 50126077578300944752567585)
          ·
            refine ⟨37594558183725708564425689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50126077578300944752567585 37594558183725708564425689)
            ·
              refine ⟨28195918637794281423319267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37594558183725708564425689 28195918637794281423319267)
              ·
                refine ⟨42293877956691422134978901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28195918637794281423319267 42293877956691422134978901)
                ·
                  refine ⟨123907845576244400786071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 42293877956691422134978901 123907845576244400786071)
                  ·
                    rfl

theorem cell23_2171787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 10].length) (baseStart_2171787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2171787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2171787 prefixEnd_2171787 := by exact prefixLift 2171787
  have htrace : WordTrace (prefixWord ++ tailWord_2171787) baseStart_2171787 baseEnd_2171787 := by
    simpa [prefixWord, tailWord_2171787, baseEnd_2171787] using wordTrace_append hprefix tailTrace_2171787
  have hstable : (prefixWord ++ tailWord_2171787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171787).length < 2 ^ (prefixWord ++ tailWord_2171787).sum := by decide
  have hdescent : baseEnd_2171787 < baseStart_2171787 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171831 : List Nat := [1, 1, 3, 1, 3, 1, 3, 1, 5, 1, 3]
def baseStart_2171831 : Nat := 118140960795 + 2171831 * 2 ^ 59
def prefixEnd_2171831 : Nat := 4983230072969 + 3 ^ 40 * 2171831 * 2
def baseEnd_2171831 : Nat := 1115193203334997434924437

theorem tailTrace_2171831 : CollatzResearch.WordTrace tailWord_2171831 prefixEnd_2171831 1115193203334997434924437 := by
  unfold tailWord_2171831
  simp only [CollatzResearch.WordTrace]
  refine ⟨79213184194834681049523347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52808789463223120699682231 79213184194834681049523347)
  ·
    refine ⟨118819776292252021574285021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79213184194834681049523347 118819776292252021574285021)
    ·
      refine ⟨44557416109594508090356883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118819776292252021574285021 44557416109594508090356883)
      ·
        refine ⟨66836124164391762135535325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44557416109594508090356883 66836124164391762135535325)
        ·
          refine ⟨25063546561646910800825747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66836124164391762135535325 25063546561646910800825747)
          ·
            refine ⟨37595319842470366201238621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25063546561646910800825747 37595319842470366201238621)
            ·
              refine ⟨14098244940926387325464483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37595319842470366201238621 14098244940926387325464483)
              ·
                refine ⟨21147367411389580988196725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14098244940926387325464483 21147367411389580988196725)
                ·
                  refine ⟨1982565694817773217643443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21147367411389580988196725 1982565694817773217643443)
                  ·
                    refine ⟨2973848542226659826465165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1982565694817773217643443 2973848542226659826465165)
                    ·
                      refine ⟨1115193203334997434924437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2973848542226659826465165 1115193203334997434924437)
                      ·
                        rfl

theorem cell23_2171831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 5, 1, 3].length) (baseStart_2171831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2171831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2171831 prefixEnd_2171831 := by exact prefixLift 2171831
  have htrace : WordTrace (prefixWord ++ tailWord_2171831) baseStart_2171831 baseEnd_2171831 := by
    simpa [prefixWord, tailWord_2171831, baseEnd_2171831] using wordTrace_append hprefix tailTrace_2171831
  have hstable : (prefixWord ++ tailWord_2171831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171831).length < 2 ^ (prefixWord ++ tailWord_2171831).sum := by decide
  have hdescent : baseEnd_2171831 < baseStart_2171831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171834 : List Nat := [3, 1, 1, 1, 2, 1, 3, 3, 3, 5]
def baseStart_2171834 : Nat := 118140960795 + 2171834 * 2 ^ 59
def prefixEnd_2171834 : Nat := 4983230072969 + 3 ^ 40 * 2171834 * 2
def baseEnd_2171834 : Nat := 371731581258986974395641

theorem tailTrace_2171834 : CollatzResearch.WordTrace tailWord_2171834 prefixEnd_2171834 371731581258986974395641 := by
  unfold tailWord_2171834
  simp only [CollatzResearch.WordTrace]
  refine ⟨19803323403455953140470639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52808862409215875041255037 19803323403455953140470639)
  ·
    refine ⟨29704985105183929710705959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19803323403455953140470639 29704985105183929710705959)
    ·
      refine ⟨44557477657775894566058939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29704985105183929710705959 44557477657775894566058939)
      ·
        refine ⟨66836216486663841849088409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44557477657775894566058939 66836216486663841849088409)
        ·
          refine ⟨50127162364997881386816307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66836216486663841849088409 50127162364997881386816307)
          ·
            refine ⟨75190743547496822080224461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50127162364997881386816307 75190743547496822080224461)
            ·
              refine ⟨28196528830311308280084173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75190743547496822080224461 28196528830311308280084173)
              ·
                refine ⟨10573698311366740605031565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28196528830311308280084173 10573698311366740605031565)
                ·
                  refine ⟨3965136866762527726886837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10573698311366740605031565 3965136866762527726886837)
                  ·
                    refine ⟨371731581258986974395641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3965136866762527726886837 371731581258986974395641)
                    ·
                      rfl

theorem cell23_2171834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 3, 5].length) (baseStart_2171834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2171834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2171834 prefixEnd_2171834 := by exact prefixLift 2171834
  have htrace : WordTrace (prefixWord ++ tailWord_2171834) baseStart_2171834 baseEnd_2171834 := by
    simpa [prefixWord, tailWord_2171834, baseEnd_2171834] using wordTrace_append hprefix tailTrace_2171834
  have hstable : (prefixWord ++ tailWord_2171834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171834).length < 2 ^ (prefixWord ++ tailWord_2171834).sum := by decide
  have hdescent : baseEnd_2171834 < baseStart_2171834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171851 : List Nat := [1, 1, 1, 1, 3, 6, 1, 3, 1, 5]
def baseStart_2171851 : Nat := 118140960795 + 2171851 * 2 ^ 59
def prefixEnd_2171851 : Nat := 4983230072969 + 3 ^ 40 * 2171851 * 2
def baseEnd_2171851 : Nat := 371734490982695785558115

theorem tailTrace_2171851 : CollatzResearch.WordTrace tailWord_2171851 prefixEnd_2171851 371734490982695785558115 := by
  unfold tailWord_2171851
  simp only [CollatzResearch.WordTrace]
  refine ⟨79213913654762224465251407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52809275769841482976834271 79213913654762224465251407)
  ·
    refine ⟨118820870482143336697877111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79213913654762224465251407 118820870482143336697877111)
    ·
      refine ⟨178231305723215005046815667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118820870482143336697877111 178231305723215005046815667)
      ·
        refine ⟨267346958584822507570223501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178231305723215005046815667 267346958584822507570223501)
        ·
          refine ⟨100255109469308440338833813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 267346958584822507570223501 100255109469308440338833813)
          ·
            refine ⟨4699458256373833140882835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 100255109469308440338833813 4699458256373833140882835)
            ·
              refine ⟨7049187384560749711324253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4699458256373833140882835 7049187384560749711324253)
              ·
                refine ⟨2643445269210281141746595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7049187384560749711324253 2643445269210281141746595)
                ·
                  refine ⟨3965167903815421712619893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2643445269210281141746595 3965167903815421712619893)
                  ·
                    refine ⟨371734490982695785558115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3965167903815421712619893 371734490982695785558115)
                    ·
                      rfl

theorem cell23_2171851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 3, 1, 5].length) (baseStart_2171851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2171851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2171851 prefixEnd_2171851 := by exact prefixLift 2171851
  have htrace : WordTrace (prefixWord ++ tailWord_2171851) baseStart_2171851 baseEnd_2171851 := by
    simpa [prefixWord, tailWord_2171851, baseEnd_2171851] using wordTrace_append hprefix tailTrace_2171851
  have hstable : (prefixWord ++ tailWord_2171851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171851).length < 2 ^ (prefixWord ++ tailWord_2171851).sum := by decide
  have hdescent : baseEnd_2171851 < baseStart_2171851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171865 : List Nat := [1, 2, 1, 2, 5, 1, 2, 4, 1, 1, 3]
def baseStart_2171865 : Nat := 118140960795 + 2171865 * 2 ^ 59
def prefixEnd_2171865 : Nat := 4983230072969 + 3 ^ 40 * 2171865 * 2
def baseEnd_2171865 : Nat := 1115210661677250301899281

theorem tailTrace_2171865 : CollatzResearch.WordTrace tailWord_2171865 prefixEnd_2171865 1115210661677250301899281 := by
  unfold tailWord_2171865
  simp only [CollatzResearch.WordTrace]
  refine ⟨79214424276711504856261049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52809616184474336570840699 79214424276711504856261049)
  ·
    refine ⟨59410818207533628642195787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79214424276711504856261049 59410818207533628642195787)
    ·
      refine ⟨89116227311300442963293681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59410818207533628642195787 89116227311300442963293681)
      ·
        refine ⟨66837170483475332222470261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89116227311300442963293681 66837170483475332222470261)
        ·
          refine ⟨6265984732825812395856587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 66837170483475332222470261 6265984732825812395856587)
          ·
            refine ⟨9398977099238718593784881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6265984732825812395856587 9398977099238718593784881)
            ·
              refine ⟨7049232824429038945338661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9398977099238718593784881 7049232824429038945338661)
              ·
                refine ⟨1321731154580444802250999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7049232824429038945338661 1321731154580444802250999)
                ·
                  refine ⟨1982596731870667203376499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1321731154580444802250999 1982596731870667203376499)
                  ·
                    refine ⟨2973895097806000805064749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1982596731870667203376499 2973895097806000805064749)
                    ·
                      refine ⟨1115210661677250301899281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2973895097806000805064749 1115210661677250301899281)
                      ·
                        rfl

theorem cell23_2171865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 4, 1, 1, 3].length) (baseStart_2171865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2171865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2171865 prefixEnd_2171865 := by exact prefixLift 2171865
  have htrace : WordTrace (prefixWord ++ tailWord_2171865) baseStart_2171865 baseEnd_2171865 := by
    simpa [prefixWord, tailWord_2171865, baseEnd_2171865] using wordTrace_append hprefix tailTrace_2171865
  have hstable : (prefixWord ++ tailWord_2171865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171865).length < 2 ^ (prefixWord ++ tailWord_2171865).sum := by decide
  have hdescent : baseEnd_2171865 < baseStart_2171865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171932 : List Nat := [2, 2, 3, 1, 4, 2, 2, 1, 2, 4]
def baseStart_2171932 : Nat := 118140960795 + 2171932 * 2 ^ 59
def prefixEnd_2171932 : Nat := 4983230072969 + 3 ^ 40 * 2171932 * 2
def baseEnd_2171932 : Nat := 371748354960367179920491

theorem tailTrace_2171932 : CollatzResearch.WordTrace tailWord_2171932 prefixEnd_2171932 371748354960367179920491 := by
  unfold tailWord_2171932
  simp only [CollatzResearch.WordTrace]
  refine ⟨39608433983734387649475025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52811245311645850199300033 39608433983734387649475025)
  ·
    refine ⟨29706325487800790737106269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39608433983734387649475025 29706325487800790737106269)
    ·
      refine ⟨11139872057925296526414851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29706325487800790737106269 11139872057925296526414851)
      ·
        refine ⟨16709808086887944789622277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11139872057925296526414851 16709808086887944789622277)
        ·
          refine ⟨3133089016291489648054177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16709808086887944789622277 3133089016291489648054177)
          ·
            refine ⟨2349816762218617236040633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3133089016291489648054177 2349816762218617236040633)
            ·
              refine ⟨1762362571663962927030475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2349816762218617236040633 1762362571663962927030475)
              ·
                refine ⟨2643543857495944390545713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1762362571663962927030475 2643543857495944390545713)
                ·
                  refine ⟨1982657893121958292909285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2643543857495944390545713 1982657893121958292909285)
                  ·
                    refine ⟨371748354960367179920491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1982657893121958292909285 371748354960367179920491)
                    ·
                      rfl

theorem cell23_2171932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 1, 2, 4].length) (baseStart_2171932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2171932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2171932 prefixEnd_2171932 := by exact prefixLift 2171932
  have htrace : WordTrace (prefixWord ++ tailWord_2171932) baseStart_2171932 baseEnd_2171932 := by
    simpa [prefixWord, tailWord_2171932, baseEnd_2171932] using wordTrace_append hprefix tailTrace_2171932
  have hstable : (prefixWord ++ tailWord_2171932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171932).length < 2 ^ (prefixWord ++ tailWord_2171932).sum := by decide
  have hdescent : baseEnd_2171932 < baseStart_2171932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171948 : List Nat := [2, 2, 1, 1, 1, 2, 5, 1, 3, 3, 2]
def baseStart_2171948 : Nat := 118140960795 + 2171948 * 2 ^ 59
def prefixEnd_2171948 : Nat := 4983230072969 + 3 ^ 40 * 2171948 * 2
def baseEnd_2171948 : Nat := 1115253280571573477161399

theorem tailTrace_2171948 : CollatzResearch.WordTrace tailWord_2171948 prefixEnd_2171948 1115253280571573477161399 := by
  unfold tailWord_2171948
  simp only [CollatzResearch.WordTrace]
  refine ⟨39608725767705405015766249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52811634356940540021021665 39608725767705405015766249)
  ·
    refine ⟨29706544325779053761824687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39608725767705405015766249 29706544325779053761824687)
    ·
      refine ⟨44559816488668580642737031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29706544325779053761824687 44559816488668580642737031)
      ·
        refine ⟨66839724733002870964105547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44559816488668580642737031 66839724733002870964105547)
        ·
          refine ⟨100259587099504306446158321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66839724733002870964105547 100259587099504306446158321)
          ·
            refine ⟨75194690324628229834618741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100259587099504306446158321 75194690324628229834618741)
            ·
              refine ⟨7049502217933896546995507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 75194690324628229834618741 7049502217933896546995507)
              ·
                refine ⟨10574253326900844820493261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7049502217933896546995507 10574253326900844820493261)
                ·
                  refine ⟨3965344997587816807684973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10574253326900844820493261 3965344997587816807684973)
                  ·
                    refine ⟨1487004374095431302881865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3965344997587816807684973 1487004374095431302881865)
                    ·
                      refine ⟨1115253280571573477161399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1487004374095431302881865 1115253280571573477161399)
                      ·
                        rfl

theorem cell23_2171948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 3, 2].length) (baseStart_2171948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2171948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2171948 prefixEnd_2171948 := by exact prefixLift 2171948
  have htrace : WordTrace (prefixWord ++ tailWord_2171948) baseStart_2171948 baseEnd_2171948 := by
    simpa [prefixWord, tailWord_2171948, baseEnd_2171948] using wordTrace_append hprefix tailTrace_2171948
  have hstable : (prefixWord ++ tailWord_2171948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171948).length < 2 ^ (prefixWord ++ tailWord_2171948).sum := by decide
  have hdescent : baseEnd_2171948 < baseStart_2171948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171984 : List Nat := [2, 1, 1, 1, 1, 3, 1, 2, 11]
def baseStart_2171984 : Nat := 118140960795 + 2171984 * 2 ^ 59
def prefixEnd_2171984 : Nat := 4983230072969 + 3 ^ 40 * 2171984 * 2
def baseEnd_2171984 : Nat := 123919085097237259590137

theorem tailTrace_2171984 : CollatzResearch.WordTrace tailWord_2171984 prefixEnd_2171984 123919085097237259590137 := by
  unfold tailWord_2171984
  simp only [CollatzResearch.WordTrace]
  refine ⟨39609382281640194089921503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52812509708853592119895337 39609382281640194089921503)
  ·
    refine ⟨59414073422460291134882255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39609382281640194089921503 59414073422460291134882255)
    ·
      refine ⟨89121110133690436702323383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59414073422460291134882255 89121110133690436702323383)
      ·
        refine ⟨133681665200535655053485075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89121110133690436702323383 133681665200535655053485075)
        ·
          refine ⟨200522497800803482580227613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133681665200535655053485075 200522497800803482580227613)
          ·
            refine ⟨75195936675301305967585355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 200522497800803482580227613 75195936675301305967585355)
            ·
              refine ⟨112793905012951958951378033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75195936675301305967585355 112793905012951958951378033)
              ·
                refine ⟨84595428759713969213533525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112793905012951958951378033 84595428759713969213533525)
                ·
                  refine ⟨123919085097237259590137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 84595428759713969213533525 123919085097237259590137)
                  ·
                    rfl

theorem cell23_2171984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 11].length) (baseStart_2171984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2171984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2171984 prefixEnd_2171984 := by exact prefixLift 2171984
  have htrace : WordTrace (prefixWord ++ tailWord_2171984) baseStart_2171984 baseEnd_2171984 := by
    simpa [prefixWord, tailWord_2171984, baseEnd_2171984] using wordTrace_append hprefix tailTrace_2171984
  have hstable : (prefixWord ++ tailWord_2171984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171984).length < 2 ^ (prefixWord ++ tailWord_2171984).sum := by decide
  have hdescent : baseEnd_2171984 < baseStart_2171984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172051 : List Nat := [1, 1, 1, 2, 1, 2, 5, 2, 1, 3, 4]
def baseStart_2172051 : Nat := 118140960795 + 2172051 * 2 ^ 59
def prefixEnd_2172051 : Nat := 4983230072969 + 3 ^ 40 * 2172051 * 2
def baseEnd_2172051 : Nat := 1115306169078986574173425

theorem tailTrace_2172051 : CollatzResearch.WordTrace tailWord_2172051 prefixEnd_2172051 1115306169078986574173425 := by
  unfold tailWord_2172051
  simp only [CollatzResearch.WordTrace]
  refine ⟨79221208254037658622532007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52814138836025105748354671 79221208254037658622532007)
  ·
    refine ⟨118831812381056487933798011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79221208254037658622532007 118831812381056487933798011)
    ·
      refine ⟨178247718571584731900697017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118831812381056487933798011 178247718571584731900697017)
      ·
        refine ⟨133685788928688548925522763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178247718571584731900697017 133685788928688548925522763)
        ·
          refine ⟨200528683393032823388284145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133685788928688548925522763 200528683393032823388284145)
          ·
            refine ⟨150396512544774617541213109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200528683393032823388284145 150396512544774617541213109)
            ·
              refine ⟨14099673051072620394488729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 150396512544774617541213109 14099673051072620394488729)
              ·
                refine ⟨10574754788304465295866547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14099673051072620394488729 10574754788304465295866547)
                ·
                  refine ⟨15862132182456697943799821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10574754788304465295866547 15862132182456697943799821)
                  ·
                    refine ⟨5948299568421261728924933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15862132182456697943799821 5948299568421261728924933)
                    ·
                      refine ⟨1115306169078986574173425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5948299568421261728924933 1115306169078986574173425)
                      ·
                        rfl

theorem cell23_2172051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 3, 4].length) (baseStart_2172051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2172051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2172051 prefixEnd_2172051 := by exact prefixLift 2172051
  have htrace : WordTrace (prefixWord ++ tailWord_2172051) baseStart_2172051 baseEnd_2172051 := by
    simpa [prefixWord, tailWord_2172051, baseEnd_2172051] using wordTrace_append hprefix tailTrace_2172051
  have hstable : (prefixWord ++ tailWord_2172051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172051).length < 2 ^ (prefixWord ++ tailWord_2172051).sum := by decide
  have hdescent : baseEnd_2172051 < baseStart_2172051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172061 : List Nat := [1, 4, 2, 1, 1, 2, 1, 1, 2, 8]
def baseStart_2172061 : Nat := 118140960795 + 2172061 * 2 ^ 59
def prefixEnd_2172061 : Nat := 4983230072969 + 3 ^ 40 * 2172061 * 2
def baseEnd_2172061 : Nat := 371770434628510511682793

theorem tailTrace_2172061 : CollatzResearch.WordTrace tailWord_2172061 prefixEnd_2172061 371770434628510511682793 := by
  unfold tailWord_2172061
  simp only [CollatzResearch.WordTrace]
  refine ⟨79221572984001430330396037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52814381989334286886930691 79221572984001430330396037)
  ·
    refine ⟨14854044934500268186949257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79221572984001430330396037 14854044934500268186949257)
    ·
      refine ⟨11140533700875201140211943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14854044934500268186949257 11140533700875201140211943)
      ·
        refine ⟨16710800551312801710317915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11140533700875201140211943 16710800551312801710317915)
        ·
          refine ⟨25066200826969202565476873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16710800551312801710317915 25066200826969202565476873)
          ·
            refine ⟨18799650620226901924107655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25066200826969202565476873 18799650620226901924107655)
            ·
              refine ⟨28199475930340352886161483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18799650620226901924107655 28199475930340352886161483)
              ·
                refine ⟨42299213895510529329242225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28199475930340352886161483 42299213895510529329242225)
                ·
                  refine ⟨31724410421632896996931669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42299213895510529329242225 31724410421632896996931669)
                  ·
                    refine ⟨371770434628510511682793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 31724410421632896996931669 371770434628510511682793)
                    ·
                      rfl

theorem cell23_2172061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_2172061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2172061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2172061 prefixEnd_2172061 := by exact prefixLift 2172061
  have htrace : WordTrace (prefixWord ++ tailWord_2172061) baseStart_2172061 baseEnd_2172061 := by
    simpa [prefixWord, tailWord_2172061, baseEnd_2172061] using wordTrace_append hprefix tailTrace_2172061
  have hstable : (prefixWord ++ tailWord_2172061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172061).length < 2 ^ (prefixWord ++ tailWord_2172061).sum := by decide
  have hdescent : baseEnd_2172061 < baseStart_2172061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172068 : List Nat := [2, 3, 1, 2, 3, 1, 2, 1, 1, 3, 4]
def baseStart_2172068 : Nat := 118140960795 + 2172068 * 2 ^ 59
def prefixEnd_2172068 : Nat := 4983230072969 + 3 ^ 40 * 2172068 * 2
def baseEnd_2172068 : Nat := 1115314898250113007660847

theorem tailTrace_2172068 : CollatzResearch.WordTrace tailWord_2172068 prefixEnd_2172068 1115314898250113007660847 := by
  unfold tailWord_2172068
  simp only [CollatzResearch.WordTrace]
  refine ⟨39610914147488035262950429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52814552196650713683933905 39610914147488035262950429)
  ·
    refine ⟨14854092805308013223606411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39610914147488035262950429 14854092805308013223606411)
    ·
      refine ⟨22281139207962019835409617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14854092805308013223606411 22281139207962019835409617)
      ·
        refine ⟨16710854405971514876557213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22281139207962019835409617 16710854405971514876557213)
        ·
          refine ⟨6266570402239318078708955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16710854405971514876557213 6266570402239318078708955)
          ·
            refine ⟨9399855603358977118063433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6266570402239318078708955 9399855603358977118063433)
            ·
              refine ⟨7049891702519232838547575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9399855603358977118063433 7049891702519232838547575)
              ·
                refine ⟨10574837553778849257821363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7049891702519232838547575 10574837553778849257821363)
                ·
                  refine ⟨15862256330668273886732045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10574837553778849257821363 15862256330668273886732045)
                  ·
                    refine ⟨5948346124000602707524517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15862256330668273886732045 5948346124000602707524517)
                    ·
                      refine ⟨1115314898250113007660847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5948346124000602707524517 1115314898250113007660847)
                      ·
                        rfl

theorem cell23_2172068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_2172068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2172068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2172068 prefixEnd_2172068 := by exact prefixLift 2172068
  have htrace : WordTrace (prefixWord ++ tailWord_2172068) baseStart_2172068 baseEnd_2172068 := by
    simpa [prefixWord, tailWord_2172068, baseEnd_2172068] using wordTrace_append hprefix tailTrace_2172068
  have hstable : (prefixWord ++ tailWord_2172068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172068).length < 2 ^ (prefixWord ++ tailWord_2172068).sum := by decide
  have hdescent : baseEnd_2172068 < baseStart_2172068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172086 : List Nat := [5, 1, 3, 2, 1, 1, 3, 2, 5]
def baseStart_2172086 : Nat := 118140960795 + 2172086 * 2 ^ 59
def prefixEnd_2172086 : Nat := 4983230072969 + 3 ^ 40 * 2172086 * 2
def baseEnd_2172086 : Nat := 123924904544654881915085

theorem tailTrace_2172086 : CollatzResearch.WordTrace tailWord_2172086 prefixEnd_2172086 123924904544654881915085 := by
  unfold tailWord_2172086
  simp only [CollatzResearch.WordTrace]
  refine ⟨4951405300556928725003507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52814989872607239733370741 4951405300556928725003507)
  ·
    refine ⟨7427107950835393087505261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4951405300556928725003507 7427107950835393087505261)
    ·
      refine ⟨2785165481563272407814473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7427107950835393087505261 2785165481563272407814473)
      ·
        refine ⟨2088874111172454305860855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2785165481563272407814473 2088874111172454305860855)
        ·
          refine ⟨3133311166758681458791283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2088874111172454305860855 3133311166758681458791283)
          ·
            refine ⟨4699966750138022188186925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3133311166758681458791283 4699966750138022188186925)
            ·
              refine ⟨1762487531301758320570097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4699966750138022188186925 1762487531301758320570097)
              ·
                refine ⟨1321865648476318740427573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1762487531301758320570097 1321865648476318740427573)
                ·
                  refine ⟨123924904544654881915085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1321865648476318740427573 123924904544654881915085)
                  ·
                    rfl

theorem cell23_2172086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 2, 5].length) (baseStart_2172086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2172086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2172086 prefixEnd_2172086 := by exact prefixLift 2172086
  have htrace : WordTrace (prefixWord ++ tailWord_2172086) baseStart_2172086 baseEnd_2172086 := by
    simpa [prefixWord, tailWord_2172086, baseEnd_2172086] using wordTrace_append hprefix tailTrace_2172086
  have hstable : (prefixWord ++ tailWord_2172086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172086).length < 2 ^ (prefixWord ++ tailWord_2172086).sum := by decide
  have hdescent : baseEnd_2172086 < baseStart_2172086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172095 : List Nat := [1, 1, 2, 2, 2, 2, 2, 6, 1, 4]
def baseStart_2172095 : Nat := 118140960795 + 2172095 * 2 ^ 59
def prefixEnd_2172095 : Nat := 4983230072969 + 3 ^ 40 * 2172095 * 2
def baseEnd_2172095 : Nat := 371776254075928134007741

theorem tailTrace_2172095 : CollatzResearch.WordTrace tailWord_2172095 prefixEnd_2172095 371776254075928134007741 := by
  unfold tailWord_2172095
  simp only [CollatzResearch.WordTrace]
  refine ⟨79222813065878254137133739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52815208710585502758089159 79222813065878254137133739)
  ·
    refine ⟨118834219598817381205700609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79222813065878254137133739 118834219598817381205700609)
    ·
      refine ⟨89125664699113035904275457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118834219598817381205700609 89125664699113035904275457)
      ·
        refine ⟨66844248524334776928206593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89125664699113035904275457 66844248524334776928206593)
        ·
          refine ⟨50133186393251082696154945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66844248524334776928206593 50133186393251082696154945)
          ·
            refine ⟨37599889794938312022116209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50133186393251082696154945 37599889794938312022116209)
            ·
              refine ⟨28199917346203734016587157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37599889794938312022116209 28199917346203734016587157)
              ·
                refine ⟨1321871125603300032027523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28199917346203734016587157 1321871125603300032027523)
                ·
                  refine ⟨1982806688404950048041285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1321871125603300032027523 1982806688404950048041285)
                  ·
                    refine ⟨371776254075928134007741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1982806688404950048041285 371776254075928134007741)
                    ·
                      rfl

theorem cell23_2172095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 6, 1, 4].length) (baseStart_2172095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2172095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2172095 prefixEnd_2172095 := by exact prefixLift 2172095
  have htrace : WordTrace (prefixWord ++ tailWord_2172095) baseStart_2172095 baseEnd_2172095 := by
    simpa [prefixWord, tailWord_2172095, baseEnd_2172095] using wordTrace_append hprefix tailTrace_2172095
  have hstable : (prefixWord ++ tailWord_2172095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172095).length < 2 ^ (prefixWord ++ tailWord_2172095).sum := by decide
  have hdescent : baseEnd_2172095 < baseStart_2172095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172146 : List Nat := [3, 2, 1, 3, 3, 2, 2, 2, 1, 4]
def baseStart_2172146 : Nat := 118140960795 + 2172146 * 2 ^ 59
def prefixEnd_2172146 : Nat := 4983230072969 + 3 ^ 40 * 2172146 * 2
def baseEnd_2172146 : Nat := 371784983247054567495163

theorem tailTrace_2172146 : CollatzResearch.WordTrace tailWord_2172146 prefixEnd_2172146 371784983247054567495163 := by
  unfold tailWord_2172146
  simp only [CollatzResearch.WordTrace]
  refine ⟨19806168297173372461810073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52816448792462326564826861 19806168297173372461810073)
  ·
    refine ⟨14854626222880029346357555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19806168297173372461810073 14854626222880029346357555)
    ·
      refine ⟨22281939334320044019536333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14854626222880029346357555 22281939334320044019536333)
      ·
        refine ⟨8355727250370016507326125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22281939334320044019536333 8355727250370016507326125)
        ·
          refine ⟨3133397718888756190247297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8355727250370016507326125 3133397718888756190247297)
          ·
            refine ⟨2350048289166567142685473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3133397718888756190247297 2350048289166567142685473)
            ·
              refine ⟨1762536216874925357014105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2350048289166567142685473 1762536216874925357014105)
              ·
                refine ⟨1321902162656194017760579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1762536216874925357014105 1321902162656194017760579)
                ·
                  refine ⟨1982853243984291026640869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1321902162656194017760579 1982853243984291026640869)
                  ·
                    refine ⟨371784983247054567495163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1982853243984291026640869 371784983247054567495163)
                    ·
                      rfl

theorem cell23_2172146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 2, 1, 4].length) (baseStart_2172146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2172146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2172146 prefixEnd_2172146 := by exact prefixLift 2172146
  have htrace : WordTrace (prefixWord ++ tailWord_2172146) baseStart_2172146 baseEnd_2172146 := by
    simpa [prefixWord, tailWord_2172146, baseEnd_2172146] using wordTrace_append hprefix tailTrace_2172146
  have hstable : (prefixWord ++ tailWord_2172146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172146).length < 2 ^ (prefixWord ++ tailWord_2172146).sum := by decide
  have hdescent : baseEnd_2172146 < baseStart_2172146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172189 : List Nat := [1, 4, 2, 3, 1, 3, 2, 1, 1, 5]
def baseStart_2172189 : Nat := 118140960795 + 2172189 * 2 ^ 59
def prefixEnd_2172189 : Nat := 4983230072969 + 3 ^ 40 * 2172189 * 2
def baseEnd_2172189 : Nat := 371792343136435678082597

theorem tailTrace_2172189 : CollatzResearch.WordTrace tailWord_2172189 prefixEnd_2172189 371792343136435678082597 := by
  unfold tailWord_2172189
  simp only [CollatzResearch.WordTrace]
  refine ⟨79226241527537708191055621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52817494351691805460703747 79226241527537708191055621)
  ·
    refine ⟨14854920286413320285822929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79226241527537708191055621 14854920286413320285822929)
    ·
      refine ⟨11141190214809990214367197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14854920286413320285822929 11141190214809990214367197)
      ·
        refine ⟨4177946330553746330387699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11141190214809990214367197 4177946330553746330387699)
        ·
          refine ⟨6266919495830619495581549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4177946330553746330387699 6266919495830619495581549)
          ·
            refine ⟨2350094810936482310843081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6266919495830619495581549 2350094810936482310843081)
            ·
              refine ⟨1762571108202361733132311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2350094810936482310843081 1762571108202361733132311)
              ·
                refine ⟨2643856662303542599698467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1762571108202361733132311 2643856662303542599698467)
                ·
                  refine ⟨3965784993455313899547701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2643856662303542599698467 3965784993455313899547701)
                  ·
                    refine ⟨371792343136435678082597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3965784993455313899547701 371792343136435678082597)
                    ·
                      rfl

theorem cell23_2172189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 1, 1, 5].length) (baseStart_2172189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2172189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2172189 prefixEnd_2172189 := by exact prefixLift 2172189
  have htrace : WordTrace (prefixWord ++ tailWord_2172189) baseStart_2172189 baseEnd_2172189 := by
    simpa [prefixWord, tailWord_2172189, baseEnd_2172189] using wordTrace_append hprefix tailTrace_2172189
  have hstable : (prefixWord ++ tailWord_2172189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172189).length < 2 ^ (prefixWord ++ tailWord_2172189).sum := by decide
  have hdescent : baseEnd_2172189 < baseStart_2172189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172192 : List Nat := [2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 4]
def baseStart_2172192 : Nat := 118140960795 + 2172192 * 2 ^ 59
def prefixEnd_2172192 : Nat := 4983230072969 + 3 ^ 40 * 2172192 * 2
def baseEnd_2172192 : Nat := 1115378569851270522510277

theorem tailTrace_2172192 : CollatzResearch.WordTrace tailWord_2172192 prefixEnd_2172192 1115378569851270522510277 := by
  unfold tailWord_2172192
  simp only [CollatzResearch.WordTrace]
  refine ⟨39613175473263419851707415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52817567297684559802276553 39613175473263419851707415)
  ·
    refine ⟨59419763209895129777561123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39613175473263419851707415 59419763209895129777561123)
    ·
      refine ⟨89129644814842694666341685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59419763209895129777561123 89129644814842694666341685)
      ·
        refine ⟨8355904201391502624969533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 89129644814842694666341685 8355904201391502624969533)
        ·
          refine ⟨3133464075521813484363575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8355904201391502624969533 3133464075521813484363575)
          ·
            refine ⟨4700196113282720226545363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3133464075521813484363575 4700196113282720226545363)
            ·
              refine ⟨7050294169924080339818045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4700196113282720226545363 7050294169924080339818045)
              ·
                refine ⟨2643860313721530127431767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7050294169924080339818045 2643860313721530127431767)
                ·
                  refine ⟨3965790470582295191147651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2643860313721530127431767 3965790470582295191147651)
                  ·
                    refine ⟨5948685705873442786721477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3965790470582295191147651 5948685705873442786721477)
                    ·
                      refine ⟨1115378569851270522510277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5948685705873442786721477 1115378569851270522510277)
                      ·
                        rfl

theorem cell23_2172192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_2172192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2172192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2172192 prefixEnd_2172192 := by exact prefixLift 2172192
  have htrace : WordTrace (prefixWord ++ tailWord_2172192) baseStart_2172192 baseEnd_2172192 := by
    simpa [prefixWord, tailWord_2172192, baseEnd_2172192] using wordTrace_append hprefix tailTrace_2172192
  have hstable : (prefixWord ++ tailWord_2172192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172192).length < 2 ^ (prefixWord ++ tailWord_2172192).sum := by decide
  have hdescent : baseEnd_2172192 < baseStart_2172192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172202 : List Nat := [3, 1, 4, 2, 1, 2, 1, 1, 4, 4]
def baseStart_2172202 : Nat := 118140960795 + 2172202 * 2 ^ 59
def prefixEnd_2172202 : Nat := 4983230072969 + 3 ^ 40 * 2172202 * 2
def baseEnd_2172202 : Nat := 371794568219271827795077

theorem tailTrace_2172202 : CollatzResearch.WordTrace tailWord_2172202 prefixEnd_2172202 371794568219271827795077 := by
  unfold tailWord_2172202
  simp only [CollatzResearch.WordTrace]
  refine ⟨19806678919122652852819715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52817810450993740940852573 19806678919122652852819715)
  ·
    refine ⟨29710018378683979279229573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19806678919122652852819715 29710018378683979279229573)
    ·
      refine ⟨5570628446003246114855545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29710018378683979279229573 5570628446003246114855545)
      ·
        refine ⟨4177971334502434586141659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5570628446003246114855545 4177971334502434586141659)
        ·
          refine ⟨6266957001753651879212489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4177971334502434586141659 6266957001753651879212489)
          ·
            refine ⟨4700217751315238909409367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6266957001753651879212489 4700217751315238909409367)
            ·
              refine ⟨7050326626972858364114051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4700217751315238909409367 7050326626972858364114051)
              ·
                refine ⟨10575489940459287546171077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7050326626972858364114051 10575489940459287546171077)
                ·
                  refine ⟨1982904363836116414907077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10575489940459287546171077 1982904363836116414907077)
                  ·
                    refine ⟨371794568219271827795077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1982904363836116414907077 371794568219271827795077)
                    ·
                      rfl

theorem cell23_2172202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_2172202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2172202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2172202 prefixEnd_2172202 := by exact prefixLift 2172202
  have htrace : WordTrace (prefixWord ++ tailWord_2172202) baseStart_2172202 baseEnd_2172202 := by
    simpa [prefixWord, tailWord_2172202, baseEnd_2172202] using wordTrace_append hprefix tailTrace_2172202
  have hstable : (prefixWord ++ tailWord_2172202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172202).length < 2 ^ (prefixWord ++ tailWord_2172202).sum := by decide
  have hdescent : baseEnd_2172202 < baseStart_2172202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172209 : List Nat := [1, 2, 2, 3, 3, 2, 2, 1, 3, 2, 2]
def baseStart_2172209 : Nat := 118140960795 + 2172209 * 2 ^ 59
def prefixEnd_2172209 : Nat := 4983230072969 + 3 ^ 40 * 2172209 * 2
def baseEnd_2172209 : Nat := 1115387299022396955997699

theorem tailTrace_2172209 : CollatzResearch.WordTrace tailWord_2172209 prefixEnd_2172209 1115387299022396955997699 := by
  unfold tailWord_2172209
  simp only [CollatzResearch.WordTrace]
  refine ⟨79226970987465251606783681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52817980658310167737855787 79226970987465251606783681)
  ·
    refine ⟨59420228240598938705087761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79226970987465251606783681 59420228240598938705087761)
    ·
      refine ⟨44565171180449204028815821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59420228240598938705087761 44565171180449204028815821)
      ·
        refine ⟨16711939192668451510805933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44565171180449204028815821 16711939192668451510805933)
        ·
          refine ⟨6266977197250669316552225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16711939192668451510805933 6266977197250669316552225)
          ·
            refine ⟨4700232897938001987414169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6266977197250669316552225 4700232897938001987414169)
            ·
              refine ⟨3525174673453501490560627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4700232897938001987414169 3525174673453501490560627)
              ·
                refine ⟨5287762010180252235840941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3525174673453501490560627 5287762010180252235840941)
                ·
                  refine ⟨1982910753817594588440353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5287762010180252235840941 1982910753817594588440353)
                  ·
                    refine ⟨1487183065363195941330265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1982910753817594588440353 1487183065363195941330265)
                    ·
                      refine ⟨1115387299022396955997699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1487183065363195941330265 1115387299022396955997699)
                      ·
                        rfl

theorem cell23_2172209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 1, 3, 2, 2].length) (baseStart_2172209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2172209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2172209 prefixEnd_2172209 := by exact prefixLift 2172209
  have htrace : WordTrace (prefixWord ++ tailWord_2172209) baseStart_2172209 baseEnd_2172209 := by
    simpa [prefixWord, tailWord_2172209, baseEnd_2172209] using wordTrace_append hprefix tailTrace_2172209
  have hstable : (prefixWord ++ tailWord_2172209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172209).length < 2 ^ (prefixWord ++ tailWord_2172209).sum := by decide
  have hdescent : baseEnd_2172209 < baseStart_2172209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172235 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 7, 3, 2]
def baseStart_2172235 : Nat := 118140960795 + 2172235 * 2 ^ 59
def prefixEnd_2172235 : Nat := 4983230072969 + 3 ^ 40 * 2172235 * 2
def baseEnd_2172235 : Nat := 1115400649519413854272579

theorem tailTrace_2172235 : CollatzResearch.WordTrace tailWord_2172235 prefixEnd_2172235 1115400649519413854272579 := by
  unfold tailWord_2172235
  simp only [CollatzResearch.WordTrace]
  refine ⟨79227919285371058047230159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52818612856914038698153439 79227919285371058047230159)
  ·
    refine ⟨118841878928056587070845239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79227919285371058047230159 118841878928056587070845239)
    ·
      refine ⟨178262818392084880606267859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118841878928056587070845239 178262818392084880606267859)
      ·
        refine ⟨267394227588127320909401789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178262818392084880606267859 267394227588127320909401789)
        ·
          refine ⟨100272835345547745341025671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 267394227588127320909401789 100272835345547745341025671)
          ·
            refine ⟨150409253018321618011538507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100272835345547745341025671 150409253018321618011538507)
            ·
              refine ⟨225613879527482427017307761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150409253018321618011538507 225613879527482427017307761)
              ·
                refine ⟨169210409645611820262980821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 225613879527482427017307761 169210409645611820262980821)
                ·
                  refine ⟨3965868976069027037413613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 169210409645611820262980821 3965868976069027037413613)
                  ·
                    refine ⟨1487200866025885139030105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3965868976069027037413613 1487200866025885139030105)
                    ·
                      refine ⟨1115400649519413854272579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1487200866025885139030105 1115400649519413854272579)
                      ·
                        rfl

theorem cell23_2172235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 7, 3, 2].length) (baseStart_2172235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2172235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2172235 prefixEnd_2172235 := by exact prefixLift 2172235
  have htrace : WordTrace (prefixWord ++ tailWord_2172235) baseStart_2172235 baseEnd_2172235 := by
    simpa [prefixWord, tailWord_2172235, baseEnd_2172235] using wordTrace_append hprefix tailTrace_2172235
  have hstable : (prefixWord ++ tailWord_2172235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172235).length < 2 ^ (prefixWord ++ tailWord_2172235).sum := by decide
  have hdescent : baseEnd_2172235 < baseStart_2172235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172238 : List Nat := [4, 1, 1, 1, 1, 1, 3, 1, 1, 4, 5]
def baseStart_2172238 : Nat := 118140960795 + 2172238 * 2 ^ 59
def prefixEnd_2172238 : Nat := 4983230072969 + 3 ^ 40 * 2172238 * 2
def baseEnd_2172238 : Nat := 1115402189961377342535065

theorem tailTrace_2172238 : CollatzResearch.WordTrace tailWord_2172238 prefixEnd_2172238 1115402189961377342535065 := by
  unfold tailWord_2172238
  simp only [CollatzResearch.WordTrace]
  refine ⟨9903503588045023694948671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52818685802906793039726245 9903503588045023694948671)
  ·
    refine ⟨14855255382067535542423007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9903503588045023694948671 14855255382067535542423007)
    ·
      refine ⟨22282883073101303313634511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14855255382067535542423007 22282883073101303313634511)
      ·
        refine ⟨33424324609651954970451767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22282883073101303313634511 33424324609651954970451767)
        ·
          refine ⟨50136486914477932455677651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33424324609651954970451767 50136486914477932455677651)
          ·
            refine ⟨75204730371716898683516477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50136486914477932455677651 75204730371716898683516477)
            ·
              refine ⟨28201773889393837006318679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75204730371716898683516477 28201773889393837006318679)
              ·
                refine ⟨42302660834090755509478019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28201773889393837006318679 42302660834090755509478019)
                ·
                  refine ⟨63453991251136133264217029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42302660834090755509478019 63453991251136133264217029)
                  ·
                    refine ⟨11897623359588024987040693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 63453991251136133264217029 11897623359588024987040693)
                    ·
                      refine ⟨1115402189961377342535065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11897623359588024987040693 1115402189961377342535065)
                      ·
                        rfl

theorem cell23_2172238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_2172238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2172238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2172238 prefixEnd_2172238 := by exact prefixLift 2172238
  have htrace : WordTrace (prefixWord ++ tailWord_2172238) baseStart_2172238 baseEnd_2172238 := by
    simpa [prefixWord, tailWord_2172238, baseEnd_2172238] using wordTrace_append hprefix tailTrace_2172238
  have hstable : (prefixWord ++ tailWord_2172238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172238).length < 2 ^ (prefixWord ++ tailWord_2172238).sum := by decide
  have hdescent : baseEnd_2172238 < baseStart_2172238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172265 : List Nat := [1, 2, 1, 1, 1, 3, 2, 1, 5, 4, 2]
def baseStart_2172265 : Nat := 118140960795 + 2172265 * 2 ^ 59
def prefixEnd_2172265 : Nat := 4983230072969 + 3 ^ 40 * 2172265 * 2
def baseEnd_2172265 : Nat := 1115416053939048736897441

theorem tailTrace_2172265 : CollatzResearch.WordTrace tailWord_2172265 prefixEnd_2172265 1115416053939048736897441 := by
  unfold tailWord_2172265
  simp only [CollatzResearch.WordTrace]
  refine ⟨79229013475262373170822249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52819342316841582113881499 79229013475262373170822249)
  ·
    refine ⟨59421760106446779878116687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79229013475262373170822249 59421760106446779878116687)
    ·
      refine ⟨89132640159670169817175031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59421760106446779878116687 89132640159670169817175031)
      ·
        refine ⟨133698960239505254725762547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89132640159670169817175031 133698960239505254725762547)
        ·
          refine ⟨200548440359257882088643821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133698960239505254725762547 200548440359257882088643821)
          ·
            refine ⟨75205665134721705783241433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 200548440359257882088643821 75205665134721705783241433)
            ·
              refine ⟨56404248851041279337431075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75205665134721705783241433 56404248851041279337431075)
              ·
                refine ⟨84606373276561919006146613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56404248851041279337431075 84606373276561919006146613)
                ·
                  refine ⟨7931847494677679906826245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 84606373276561919006146613 7931847494677679906826245)
                  ·
                    refine ⟨1487221405252064982529921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7931847494677679906826245 1487221405252064982529921)
                    ·
                      refine ⟨1115416053939048736897441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1487221405252064982529921 1115416053939048736897441)
                      ·
                        rfl

theorem cell23_2172265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5, 4, 2].length) (baseStart_2172265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2172265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2172265 prefixEnd_2172265 := by exact prefixLift 2172265
  have htrace : WordTrace (prefixWord ++ tailWord_2172265) baseStart_2172265 baseEnd_2172265 := by
    simpa [prefixWord, tailWord_2172265, baseEnd_2172265] using wordTrace_append hprefix tailTrace_2172265
  have hstable : (prefixWord ++ tailWord_2172265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172265).length < 2 ^ (prefixWord ++ tailWord_2172265).sum := by decide
  have hdescent : baseEnd_2172265 < baseStart_2172265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172288 : List Nat := [2, 1, 1, 2, 1, 2, 1, 6, 7]
def baseStart_2172288 : Nat := 118140960795 + 2172288 * 2 ^ 59
def prefixEnd_2172288 : Nat := 4983230072969 + 3 ^ 40 * 2172288 * 2
def baseEnd_2172288 : Nat := 123936429332678016323315

theorem tailTrace_2172288 : CollatzResearch.WordTrace tailWord_2172288 prefixEnd_2172288 123936429332678016323315 := by
  unfold tailWord_2172288
  simp only [CollatzResearch.WordTrace]
  refine ⟨39614926177089524049454759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52819901569452698732606345 39614926177089524049454759)
  ·
    refine ⟨59422389265634286074182139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39614926177089524049454759 59422389265634286074182139)
    ·
      refine ⟨89133583898451429111273209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59422389265634286074182139 89133583898451429111273209)
      ·
        refine ⟨66850187923838571833454907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89133583898451429111273209 66850187923838571833454907)
        ·
          refine ⟨100275281885757857750182361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66850187923838571833454907 100275281885757857750182361)
          ·
            refine ⟨75206461414318393312636771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100275281885757857750182361 75206461414318393312636771)
            ·
              refine ⟨112809692121477589968955157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75206461414318393312636771 112809692121477589968955157)
              ·
                refine ⟨5287954318194262029794773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 112809692121477589968955157 5287954318194262029794773)
                ·
                  refine ⟨123936429332678016323315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5287954318194262029794773 123936429332678016323315)
                  ·
                    rfl

theorem cell23_2172288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6, 7].length) (baseStart_2172288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2172288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2172288 prefixEnd_2172288 := by exact prefixLift 2172288
  have htrace : WordTrace (prefixWord ++ tailWord_2172288) baseStart_2172288 baseEnd_2172288 := by
    simpa [prefixWord, tailWord_2172288, baseEnd_2172288] using wordTrace_append hprefix tailTrace_2172288
  have hstable : (prefixWord ++ tailWord_2172288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172288).length < 2 ^ (prefixWord ++ tailWord_2172288).sum := by decide
  have hdescent : baseEnd_2172288 < baseStart_2172288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172354 : List Nat := [3, 5, 2, 1, 1, 2, 2, 1, 1, 3, 2]
def baseStart_2172354 : Nat := 118140960795 + 2172354 * 2 ^ 59
def prefixEnd_2172354 : Nat := 4983230072969 + 3 ^ 40 * 2172354 * 2
def baseEnd_2172354 : Nat := 1115461753717298888684533

theorem tailTrace_2172354 : CollatzResearch.WordTrace tailWord_2172354 prefixEnd_2172354 1115461753717298888684533 := by
  unfold tailWord_2172354
  simp only [CollatzResearch.WordTrace]
  refine ⟨19808064892984985342703029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52821506381293294247208077 19808064892984985342703029)
  ·
    refine ⟨1857006083717342375878409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19808064892984985342703029 1857006083717342375878409)
    ·
      refine ⟨1392754562788006781908807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1857006083717342375878409 1392754562788006781908807)
      ·
        refine ⟨2089131844182010172863211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1392754562788006781908807 2089131844182010172863211)
        ·
          refine ⟨3133697766273015259294817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2089131844182010172863211 3133697766273015259294817)
          ·
            refine ⟨2350273324704761444471113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3133697766273015259294817 2350273324704761444471113)
            ·
              refine ⟨1762704993528571083353335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2350273324704761444471113 1762704993528571083353335)
              ·
                refine ⟨2644057490292856625030003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1762704993528571083353335 2644057490292856625030003)
                ·
                  refine ⟨3966086235439284937545005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2644057490292856625030003 3966086235439284937545005)
                  ·
                    refine ⟨1487282338289731851579377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3966086235439284937545005 1487282338289731851579377)
                    ·
                      refine ⟨1115461753717298888684533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1487282338289731851579377 1115461753717298888684533)
                      ·
                        rfl

theorem cell23_2172354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_2172354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2172354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2172354 prefixEnd_2172354 := by exact prefixLift 2172354
  have htrace : WordTrace (prefixWord ++ tailWord_2172354) baseStart_2172354 baseEnd_2172354 := by
    simpa [prefixWord, tailWord_2172354, baseEnd_2172354] using wordTrace_append hprefix tailTrace_2172354
  have hstable : (prefixWord ++ tailWord_2172354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172354).length < 2 ^ (prefixWord ++ tailWord_2172354).sum := by decide
  have hdescent : baseEnd_2172354 < baseStart_2172354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172389 : List Nat := [1, 3, 1, 5, 1, 1, 2, 1, 2, 4, 2]
def baseStart_2172389 : Nat := 118140960795 + 2172389 * 2 ^ 59
def prefixEnd_2172389 : Nat := 4983230072969 + 3 ^ 40 * 2172389 * 2
def baseEnd_2172389 : Nat := 1115479725540206251746871

theorem tailTrace_2172389 : CollatzResearch.WordTrace tailWord_2172389 prefixEnd_2172389 1115479725540206251746871 := by
  unfold tailWord_2172389
  simp only [CollatzResearch.WordTrace]
  refine ⟨79233536126813142348336221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52822357417875428232224147 79233536126813142348336221)
  ·
    refine ⟨29712576047554928380626083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79233536126813142348336221 29712576047554928380626083)
    ·
      refine ⟨44568864071332392570939125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29712576047554928380626083 44568864071332392570939125)
      ·
        refine ⟨4178331006687411803525543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44568864071332392570939125 4178331006687411803525543)
        ·
          refine ⟨6267496510031117705288315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4178331006687411803525543 6267496510031117705288315)
          ·
            refine ⟨9401244765046676557932473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6267496510031117705288315 9401244765046676557932473)
            ·
              refine ⟨7050933573785007418449355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9401244765046676557932473 7050933573785007418449355)
              ·
                refine ⟨10576400360677511127674033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7050933573785007418449355 10576400360677511127674033)
                ·
                  refine ⟨7932300270508133345755525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10576400360677511127674033 7932300270508133345755525)
                  ·
                    refine ⟨1487306300720275002329161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7932300270508133345755525 1487306300720275002329161)
                    ·
                      refine ⟨1115479725540206251746871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1487306300720275002329161 1115479725540206251746871)
                      ·
                        rfl

theorem cell23_2172389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_2172389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2172389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2172389 prefixEnd_2172389 := by exact prefixLift 2172389
  have htrace : WordTrace (prefixWord ++ tailWord_2172389) baseStart_2172389 baseEnd_2172389 := by
    simpa [prefixWord, tailWord_2172389, baseEnd_2172389] using wordTrace_append hprefix tailTrace_2172389
  have hstable : (prefixWord ++ tailWord_2172389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172389).length < 2 ^ (prefixWord ++ tailWord_2172389).sum := by decide
  have hdescent : baseEnd_2172389 < baseStart_2172389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172472 : List Nat := [2, 1, 2, 1, 4, 3, 1, 2, 1, 6]
def baseStart_2172472 : Nat := 118140960795 + 2172472 * 2 ^ 59
def prefixEnd_2172472 : Nat := 4983230072969 + 3 ^ 40 * 2172472 * 2
def baseEnd_2172472 : Nat := 371840781478176475669663

theorem tailTrace_2172472 : CollatzResearch.WordTrace tailWord_2172472 prefixEnd_2172472 371840781478176475669663 := by
  unfold tailWord_2172472
  simp only [CollatzResearch.WordTrace]
  refine ⟨39618281692756223761803835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52824375590341631682405113 39618281692756223761803835)
  ·
    refine ⟨59427422539134335642705753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39618281692756223761803835 59427422539134335642705753)
    ·
      refine ⟨44570566904350751732029315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59427422539134335642705753 44570566904350751732029315)
      ·
        refine ⟨66855850356526127598043973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44570566904350751732029315 66855850356526127598043973)
        ·
          refine ⟨12535471941848648924633245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66855850356526127598043973 12535471941848648924633245)
          ·
            refine ⟨4700801978193243346737467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12535471941848648924633245 4700801978193243346737467)
            ·
              refine ⟨7051202967289865020106201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4700801978193243346737467 7051202967289865020106201)
              ·
                refine ⟨5288402225467398765079651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7051202967289865020106201 5288402225467398765079651)
                ·
                  refine ⟨7932603338201098147619477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5288402225467398765079651 7932603338201098147619477)
                  ·
                    refine ⟨371840781478176475669663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7932603338201098147619477 371840781478176475669663)
                    ·
                      rfl

theorem cell23_2172472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 2, 1, 6].length) (baseStart_2172472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2172472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2172472 prefixEnd_2172472 := by exact prefixLift 2172472
  have htrace : WordTrace (prefixWord ++ tailWord_2172472) baseStart_2172472 baseEnd_2172472 := by
    simpa [prefixWord, tailWord_2172472, baseEnd_2172472] using wordTrace_append hprefix tailTrace_2172472
  have hstable : (prefixWord ++ tailWord_2172472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172472).length < 2 ^ (prefixWord ++ tailWord_2172472).sum := by decide
  have hdescent : baseEnd_2172472 < baseStart_2172472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172476 : List Nat := [2, 2, 2, 2, 4, 1, 3, 1, 1, 5]
def baseStart_2172476 : Nat := 118140960795 + 2172476 * 2 ^ 59
def prefixEnd_2172476 : Nat := 4983230072969 + 3 ^ 40 * 2172476 * 2
def baseEnd_2172476 : Nat := 371841466119049137119657

theorem tailTrace_2172476 : CollatzResearch.WordTrace tailWord_2172476 prefixEnd_2172476 371841466119049137119657 := by
  unfold tailWord_2172476
  simp only [CollatzResearch.WordTrace]
  refine ⟨39618354638748978103376641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52824472851665304137835521 39618354638748978103376641)
  ·
    refine ⟨29713765979061733577532481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39618354638748978103376641 29713765979061733577532481)
    ·
      refine ⟨22285324484296300183149361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29713765979061733577532481 22285324484296300183149361)
      ·
        refine ⟨16713993363222225137362021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22285324484296300183149361 16713993363222225137362021)
        ·
          refine ⟨3133873755604167213255379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16713993363222225137362021 3133873755604167213255379)
          ·
            refine ⟨4700810633406250819883069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3133873755604167213255379 4700810633406250819883069)
            ·
              refine ⟨1762803987527344057456151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4700810633406250819883069 1762803987527344057456151)
              ·
                refine ⟨2644205981291016086184227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1762803987527344057456151 2644205981291016086184227)
                ·
                  refine ⟨3966308971936524129276341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2644205981291016086184227 3966308971936524129276341)
                  ·
                    refine ⟨371841466119049137119657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3966308971936524129276341 371841466119049137119657)
                    ·
                      rfl

theorem cell23_2172476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 1, 1, 5].length) (baseStart_2172476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2172476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2172476 prefixEnd_2172476 := by exact prefixLift 2172476
  have htrace : WordTrace (prefixWord ++ tailWord_2172476) baseStart_2172476 baseEnd_2172476 := by
    simpa [prefixWord, tailWord_2172476, baseEnd_2172476] using wordTrace_append hprefix tailTrace_2172476
  have hstable : (prefixWord ++ tailWord_2172476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172476).length < 2 ^ (prefixWord ++ tailWord_2172476).sum := by decide
  have hdescent : baseEnd_2172476 < baseStart_2172476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172505 : List Nat := [1, 2, 1, 2, 2, 1, 1, 3, 2, 2, 6]
def baseStart_2172505 : Nat := 118140960795 + 2172505 * 2 ^ 59
def prefixEnd_2172505 : Nat := 4983230072969 + 3 ^ 40 * 2172505 * 2
def baseEnd_2172505 : Nat := 1115539289296127797896337

theorem tailTrace_2172505 : CollatzResearch.WordTrace tailWord_2172505 prefixEnd_2172505 1115539289296127797896337 := by
  unfold tailWord_2172505
  simp only [CollatzResearch.WordTrace]
  refine ⟨79237766994392894159558969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52825177996261929439705979 79237766994392894159558969)
  ·
    refine ⟨59428325245794670619669227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79237766994392894159558969 59428325245794670619669227)
    ·
      refine ⟨89142487868692005929503841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59428325245794670619669227 89142487868692005929503841)
      ·
        refine ⟨66856865901519004447127881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89142487868692005929503841 66856865901519004447127881)
        ·
          refine ⟨50142649426139253335345911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66856865901519004447127881 50142649426139253335345911)
          ·
            refine ⟨75213974139208880003018867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50142649426139253335345911 75213974139208880003018867)
            ·
              refine ⟨112820961208813320004528301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75213974139208880003018867 112820961208813320004528301)
              ·
                refine ⟨42307860453304995001698113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 112820961208813320004528301 42307860453304995001698113)
                ·
                  refine ⟨31730895339978746251273585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42307860453304995001698113 31730895339978746251273585)
                  ·
                    refine ⟨23798171504984059688455189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31730895339978746251273585 23798171504984059688455189)
                    ·
                      refine ⟨1115539289296127797896337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23798171504984059688455189 1115539289296127797896337)
                      ·
                        rfl

theorem cell23_2172505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 2, 6].length) (baseStart_2172505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2172505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2172505 prefixEnd_2172505 := by exact prefixLift 2172505
  have htrace : WordTrace (prefixWord ++ tailWord_2172505) baseStart_2172505 baseEnd_2172505 := by
    simpa [prefixWord, tailWord_2172505, baseEnd_2172505] using wordTrace_append hprefix tailTrace_2172505
  have hstable : (prefixWord ++ tailWord_2172505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172505).length < 2 ^ (prefixWord ++ tailWord_2172505).sum := by decide
  have hdescent : baseEnd_2172505 < baseStart_2172505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172530 : List Nat := [3, 2, 1, 2, 3, 2, 2, 3, 1, 2, 2]
def baseStart_2172530 : Nat := 118140960795 + 2172530 * 2 ^ 59
def prefixEnd_2172530 : Nat := 4983230072969 + 3 ^ 40 * 2172530 * 2
def baseEnd_2172530 : Nat := 1115552126312490200083723

theorem tailTrace_2172530 : CollatzResearch.WordTrace tailWord_2172530 prefixEnd_2172530 1115552126312490200083723 := by
  unfold tailWord_2172530
  simp only [CollatzResearch.WordTrace]
  refine ⟨19809669704825580857304761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52825785879534882286146029 19809669704825580857304761)
  ·
    refine ⟨14857252278619185642978571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19809669704825580857304761 14857252278619185642978571)
    ·
      refine ⟨22285878417928778464467857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14857252278619185642978571 22285878417928778464467857)
      ·
        refine ⟨16714408813446583848350893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22285878417928778464467857 16714408813446583848350893)
        ·
          refine ⟨6267903305042468943131585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16714408813446583848350893 6267903305042468943131585)
          ·
            refine ⟨4700927478781851707348689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6267903305042468943131585 4700927478781851707348689)
            ·
              refine ⟨3525695609086388780511517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4700927478781851707348689 3525695609086388780511517)
              ·
                refine ⟨1322135853407395792691819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3525695609086388780511517 1322135853407395792691819)
                ·
                  refine ⟨1983203780111093689037729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1322135853407395792691819 1983203780111093689037729)
                  ·
                    refine ⟨1487402835083320266778297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1983203780111093689037729 1487402835083320266778297)
                    ·
                      refine ⟨1115552126312490200083723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1487402835083320266778297 1115552126312490200083723)
                      ·
                        rfl

theorem cell23_2172530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 3, 1, 2, 2].length) (baseStart_2172530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2172530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2172530 prefixEnd_2172530 := by exact prefixLift 2172530
  have htrace : WordTrace (prefixWord ++ tailWord_2172530) baseStart_2172530 baseEnd_2172530 := by
    simpa [prefixWord, tailWord_2172530, baseEnd_2172530] using wordTrace_append hprefix tailTrace_2172530
  have hstable : (prefixWord ++ tailWord_2172530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172530).length < 2 ^ (prefixWord ++ tailWord_2172530).sum := by decide
  have hdescent : baseEnd_2172530 < baseStart_2172530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172533 : List Nat := [1, 3, 4, 2, 1, 1, 4, 1, 1, 2, 3]
def baseStart_2172533 : Nat := 118140960795 + 2172533 * 2 ^ 59
def prefixEnd_2172533 : Nat := 4983230072969 + 3 ^ 40 * 2172533 * 2
def baseEnd_2172533 : Nat := 1115553666754453688346209

theorem tailTrace_2172533 : CollatzResearch.WordTrace tailWord_2172533 prefixEnd_2172533 1115553666754453688346209 := by
  unfold tailWord_2172533
  simp only [CollatzResearch.WordTrace]
  refine ⟨79238788238291454941578253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52825858825527636627718835 79238788238291454941578253)
  ·
    refine ⟨29714545589359295603091845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79238788238291454941578253 29714545589359295603091845)
    ·
      refine ⟨5571477298004867925579721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29714545589359295603091845 5571477298004867925579721)
      ·
        refine ⟨4178607973503650944184791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5571477298004867925579721 4178607973503650944184791)
        ·
          refine ⟨6267911960255476416277187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4178607973503650944184791 6267911960255476416277187)
          ·
            refine ⟨9401867940383214624415781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6267911960255476416277187 9401867940383214624415781)
            ·
              refine ⟨1762850238821852742077959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9401867940383214624415781 1762850238821852742077959)
              ·
                refine ⟨2644275358232779113116939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1762850238821852742077959 2644275358232779113116939)
                ·
                  refine ⟨3966413037349168669675409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2644275358232779113116939 3966413037349168669675409)
                  ·
                    refine ⟨2974809778011876502256557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3966413037349168669675409 2974809778011876502256557)
                    ·
                      refine ⟨1115553666754453688346209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2974809778011876502256557 1115553666754453688346209)
                      ·
                        rfl

theorem cell23_2172533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_2172533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2172533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2172533 prefixEnd_2172533 := by exact prefixLift 2172533
  have htrace : WordTrace (prefixWord ++ tailWord_2172533) baseStart_2172533 baseEnd_2172533 := by
    simpa [prefixWord, tailWord_2172533, baseEnd_2172533] using wordTrace_append hprefix tailTrace_2172533
  have hstable : (prefixWord ++ tailWord_2172533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172533).length < 2 ^ (prefixWord ++ tailWord_2172533).sum := by decide
  have hdescent : baseEnd_2172533 < baseStart_2172533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172569 : List Nat := [1, 2, 1, 2, 1, 2, 2, 5, 1, 4, 2]
def baseStart_2172569 : Nat := 118140960795 + 2172569 * 2 ^ 59
def prefixEnd_2172569 : Nat := 4983230072969 + 3 ^ 40 * 2172569 * 2
def baseEnd_2172569 : Nat := 1115572152058015547496043

theorem tailTrace_2172569 : CollatzResearch.WordTrace tailWord_2172569 prefixEnd_2172569 1115572152058015547496043 := by
  unfold tailWord_2172569
  simp only [CollatzResearch.WordTrace]
  refine ⟨79240101266161033089888761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52826734177440688726592507 79240101266161033089888761)
  ·
    refine ⟨59430075949620774817416571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79240101266161033089888761 59430075949620774817416571)
    ·
      refine ⟨89145113924431162226124857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59430075949620774817416571 89145113924431162226124857)
      ·
        refine ⟨66858835443323371669593643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89145113924431162226124857 66858835443323371669593643)
        ·
          refine ⟨100288253164985057504390465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66858835443323371669593643 100288253164985057504390465)
          ·
            refine ⟨75216189873738793128292849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100288253164985057504390465 75216189873738793128292849)
            ·
              refine ⟨56412142405304094846219637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75216189873738793128292849 56412142405304094846219637)
              ·
                refine ⟨5288638350497258891833091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56412142405304094846219637 5288638350497258891833091)
                ·
                  refine ⟨7932957525745888337749637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5288638350497258891833091 7932957525745888337749637)
                  ·
                    refine ⟨1487429536077354063328057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7932957525745888337749637 1487429536077354063328057)
                    ·
                      refine ⟨1115572152058015547496043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1487429536077354063328057 1115572152058015547496043)
                      ·
                        rfl

theorem cell23_2172569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5, 1, 4, 2].length) (baseStart_2172569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2172569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2172569 prefixEnd_2172569 := by exact prefixLift 2172569
  have htrace : WordTrace (prefixWord ++ tailWord_2172569) baseStart_2172569 baseEnd_2172569 := by
    simpa [prefixWord, tailWord_2172569, baseEnd_2172569] using wordTrace_append hprefix tailTrace_2172569
  have hstable : (prefixWord ++ tailWord_2172569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172569).length < 2 ^ (prefixWord ++ tailWord_2172569).sum := by decide
  have hdescent : baseEnd_2172569 < baseStart_2172569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172589 : List Nat := [1, 5, 2, 1, 1, 1, 3, 1, 2, 1, 5]
def baseStart_2172589 : Nat := 118140960795 + 2172589 * 2 ^ 59
def prefixEnd_2172589 : Nat := 4983230072969 + 3 ^ 40 * 2172589 * 2
def baseEnd_2172589 : Nat := 1115582421671105469245951

theorem tailTrace_2172589 : CollatzResearch.WordTrace tailWord_2172589 prefixEnd_2172589 1115582421671105469245951 := by
  unfold tailWord_2172589
  simp only [CollatzResearch.WordTrace]
  refine ⟨79240830726088576505616821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52827220484059051003744547 79240830726088576505616821)
  ·
    refine ⟨7428827880570804047401577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 79240830726088576505616821 7428827880570804047401577)
    ·
      refine ⟨5571620910428103035551183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7428827880570804047401577 5571620910428103035551183)
      ·
        refine ⟨8357431365642154553326775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5571620910428103035551183 8357431365642154553326775)
        ·
          refine ⟨12536147048463231829990163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8357431365642154553326775 12536147048463231829990163)
          ·
            refine ⟨18804220572694847744985245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12536147048463231829990163 18804220572694847744985245)
            ·
              refine ⟨7051582714760567904369467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18804220572694847744985245 7051582714760567904369467)
              ·
                refine ⟨10577374072140851856554201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7051582714760567904369467 10577374072140851856554201)
                ·
                  refine ⟨7933030554105638892415651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10577374072140851856554201 7933030554105638892415651)
                  ·
                    refine ⟨11899545831158458338623477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7933030554105638892415651 11899545831158458338623477)
                    ·
                      refine ⟨1115582421671105469245951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11899545831158458338623477 1115582421671105469245951)
                      ·
                        rfl

theorem cell23_2172589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_2172589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2172589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2172589 prefixEnd_2172589 := by exact prefixLift 2172589
  have htrace : WordTrace (prefixWord ++ tailWord_2172589) baseStart_2172589 baseEnd_2172589 := by
    simpa [prefixWord, tailWord_2172589, baseEnd_2172589] using wordTrace_append hprefix tailTrace_2172589
  have hstable : (prefixWord ++ tailWord_2172589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172589).length < 2 ^ (prefixWord ++ tailWord_2172589).sum := by decide
  have hdescent : baseEnd_2172589 < baseStart_2172589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172614 : List Nat := [6, 1, 2, 1, 1, 3, 2, 1, 2, 1, 3]
def baseStart_2172614 : Nat := 118140960795 + 2172614 * 2 ^ 59
def prefixEnd_2172614 : Nat := 4983230072969 + 3 ^ 40 * 2172614 * 2
def baseEnd_2172614 : Nat := 1115595258687467871433337

theorem tailTrace_2172614 : CollatzResearch.WordTrace tailWord_2172614 prefixEnd_2172614 1115595258687467871433337 := by
  unfold tailWord_2172614
  simp only [CollatzResearch.WordTrace]
  refine ⟨2476304454718687680477403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 52827828367332003850184597 2476304454718687680477403)
  ·
    refine ⟨3714456682078031520716105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2476304454718687680477403 3714456682078031520716105)
    ·
      refine ⟨2785842511558523640537079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3714456682078031520716105 2785842511558523640537079)
      ·
        refine ⟨4178763767337785460805619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2785842511558523640537079 4178763767337785460805619)
        ·
          refine ⟨6268145651006678191208429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4178763767337785460805619 6268145651006678191208429)
          ·
            refine ⟨2350554619127504321703161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6268145651006678191208429 2350554619127504321703161)
            ·
              refine ⟨1762915964345628241277371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2350554619127504321703161 1762915964345628241277371)
              ·
                refine ⟨2644373946518442361916057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1762915964345628241277371 2644373946518442361916057)
                ·
                  refine ⟨1983280459888831771437043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2644373946518442361916057 1983280459888831771437043)
                  ·
                    refine ⟨2974920689833247657155565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1983280459888831771437043 2974920689833247657155565)
                    ·
                      refine ⟨1115595258687467871433337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2974920689833247657155565 1115595258687467871433337)
                      ·
                        rfl

theorem cell23_2172614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_2172614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2172614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2172614 prefixEnd_2172614 := by exact prefixLift 2172614
  have htrace : WordTrace (prefixWord ++ tailWord_2172614) baseStart_2172614 baseEnd_2172614 := by
    simpa [prefixWord, tailWord_2172614, baseEnd_2172614] using wordTrace_append hprefix tailTrace_2172614
  have hstable : (prefixWord ++ tailWord_2172614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172614).length < 2 ^ (prefixWord ++ tailWord_2172614).sum := by decide
  have hdescent : baseEnd_2172614 < baseStart_2172614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172620 : List Nat := [2, 2, 1, 5, 2, 1, 1, 3, 2, 2, 2]
def baseStart_2172620 : Nat := 118140960795 + 2172620 * 2 ^ 59
def prefixEnd_2172620 : Nat := 4983230072969 + 3 ^ 40 * 2172620 * 2
def baseEnd_2172620 : Nat := 1115598339571394847958309

theorem tailTrace_2172620 : CollatzResearch.WordTrace tailWord_2172620 prefixEnd_2172620 1115598339571394847958309 := by
  unfold tailWord_2172620
  simp only [CollatzResearch.WordTrace]
  refine ⟨39620980694488134399997657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52827974259317512533330209 39620980694488134399997657)
  ·
    refine ⟨29715735520866100799998243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39620980694488134399997657 29715735520866100799998243)
    ·
      refine ⟨44573603281299151199997365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29715735520866100799998243 44573603281299151199997365)
      ·
        refine ⟨4178775307621795424999753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44573603281299151199997365 4178775307621795424999753)
        ·
          refine ⟨3134081480716346568749815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4178775307621795424999753 3134081480716346568749815)
          ·
            refine ⟨4701122221074519853124723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3134081480716346568749815 4701122221074519853124723)
            ·
              refine ⟨7051683331611779779687085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4701122221074519853124723 7051683331611779779687085)
              ·
                refine ⟨2644381249354417417382657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7051683331611779779687085 2644381249354417417382657)
                ·
                  refine ⟨1983285937015813063036993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2644381249354417417382657 1983285937015813063036993)
                  ·
                    refine ⟨1487464452761859797277745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1983285937015813063036993 1487464452761859797277745)
                    ·
                      refine ⟨1115598339571394847958309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1487464452761859797277745 1115598339571394847958309)
                      ·
                        rfl

theorem cell23_2172620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_2172620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2172620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2172620 prefixEnd_2172620 := by exact prefixLift 2172620
  have htrace : WordTrace (prefixWord ++ tailWord_2172620) baseStart_2172620 baseEnd_2172620 := by
    simpa [prefixWord, tailWord_2172620, baseEnd_2172620] using wordTrace_append hprefix tailTrace_2172620
  have hstable : (prefixWord ++ tailWord_2172620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172620).length < 2 ^ (prefixWord ++ tailWord_2172620).sum := by decide
  have hdescent : baseEnd_2172620 < baseStart_2172620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172632 : List Nat := [2, 1, 2, 2, 3, 1, 1, 2, 1, 1, 7]
def baseStart_2172632 : Nat := 118140960795 + 2172632 * 2 ^ 59
def prefixEnd_2172632 : Nat := 4983230072969 + 3 ^ 40 * 2172632 * 2
def baseEnd_2172632 : Nat := 1115604501339248801008253

theorem tailTrace_2172632 : CollatzResearch.WordTrace tailWord_2172632 prefixEnd_2172632 1115604501339248801008253 := by
  unfold tailWord_2172632
  simp only [CollatzResearch.WordTrace]
  refine ⟨39621199532466397424716075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52828266043288529899621433 39621199532466397424716075)
  ·
    refine ⟨59431799298699596137074113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39621199532466397424716075 59431799298699596137074113)
    ·
      refine ⟨44573849474024697102805585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59431799298699596137074113 44573849474024697102805585)
      ·
        refine ⟨33430387105518522827104189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44573849474024697102805585 33430387105518522827104189)
        ·
          refine ⟨12536395164569446060164071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33430387105518522827104189 12536395164569446060164071)
          ·
            refine ⟨18804592746854169090246107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12536395164569446060164071 18804592746854169090246107)
            ·
              refine ⟨28206889120281253635369161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18804592746854169090246107 28206889120281253635369161)
              ·
                refine ⟨21155166840210940226526871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28206889120281253635369161 21155166840210940226526871)
                ·
                  refine ⟨31732750260316410339790307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21155166840210940226526871 31732750260316410339790307)
                  ·
                    refine ⟨47599125390474615509685461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31732750260316410339790307 47599125390474615509685461)
                    ·
                      refine ⟨1115604501339248801008253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 47599125390474615509685461 1115604501339248801008253)
                      ·
                        rfl

theorem cell23_2172632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_2172632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2172632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2172632 prefixEnd_2172632 := by exact prefixLift 2172632
  have htrace : WordTrace (prefixWord ++ tailWord_2172632) baseStart_2172632 baseEnd_2172632 := by
    simpa [prefixWord, tailWord_2172632, baseEnd_2172632] using wordTrace_append hprefix tailTrace_2172632
  have hstable : (prefixWord ++ tailWord_2172632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172632).length < 2 ^ (prefixWord ++ tailWord_2172632).sum := by decide
  have hdescent : baseEnd_2172632 < baseStart_2172632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172639 : List Nat := [1, 1, 2, 3, 2, 2, 4, 1, 2, 5]
def baseStart_2172639 : Nat := 118140960795 + 2172639 * 2 ^ 59
def prefixEnd_2172639 : Nat := 4983230072969 + 3 ^ 40 * 2172639 * 2
def baseEnd_2172639 : Nat := 371869365234610091206907

theorem tailTrace_2172639 : CollatzResearch.WordTrace tailWord_2172639 prefixEnd_2172639 371869365234610091206907 := by
  unfold tailWord_2172639
  simp only [CollatzResearch.WordTrace]
  refine ⟨79242654375907435044936971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52828436250604956696624647 79242654375907435044936971)
  ·
    refine ⟨118863981563861152567405457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79242654375907435044936971 118863981563861152567405457)
    ·
      refine ⟨89147986172895864425554093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118863981563861152567405457 89147986172895864425554093)
      ·
        refine ⟨33430494814835949159582785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89147986172895864425554093 33430494814835949159582785)
        ·
          refine ⟨25072871111126961869687089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33430494814835949159582785 25072871111126961869687089)
          ·
            refine ⟨18804653333345221402265317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25072871111126961869687089 18804653333345221402265317)
            ·
              refine ⟨3525872500002229012924747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18804653333345221402265317 3525872500002229012924747)
              ·
                refine ⟨5288808750003343519387121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3525872500002229012924747 5288808750003343519387121)
                ·
                  refine ⟨3966606562502507639540341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5288808750003343519387121 3966606562502507639540341)
                  ·
                    refine ⟨371869365234610091206907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3966606562502507639540341 371869365234610091206907)
                    ·
                      rfl

theorem cell23_2172639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 1, 2, 5].length) (baseStart_2172639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2172639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2172639 prefixEnd_2172639 := by exact prefixLift 2172639
  have htrace : WordTrace (prefixWord ++ tailWord_2172639) baseStart_2172639 baseEnd_2172639 := by
    simpa [prefixWord, tailWord_2172639, baseEnd_2172639] using wordTrace_append hprefix tailTrace_2172639
  have hstable : (prefixWord ++ tailWord_2172639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172639).length < 2 ^ (prefixWord ++ tailWord_2172639).sum := by decide
  have hdescent : baseEnd_2172639 < baseStart_2172639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172659 : List Nat := [1, 1, 1, 2, 2, 3, 4, 2, 2, 1, 4]
def baseStart_2172659 : Nat := 118140960795 + 2172659 * 2 ^ 59
def prefixEnd_2172659 : Nat := 4983230072969 + 3 ^ 40 * 2172659 * 2
def baseEnd_2172659 : Nat := 1115618365316920195370629

theorem tailTrace_2172659 : CollatzResearch.WordTrace tailWord_2172659 prefixEnd_2172659 1115618365316920195370629 := by
  unfold tailWord_2172659
  simp only [CollatzResearch.WordTrace]
  refine ⟨79243383835834978460665031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52828922557223318973776687 79243383835834978460665031)
  ·
    refine ⟨118865075753752467690997547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79243383835834978460665031 118865075753752467690997547)
    ·
      refine ⟨178297613630628701536496321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118865075753752467690997547 178297613630628701536496321)
      ·
        refine ⟨133723210222971526152372241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178297613630628701536496321 133723210222971526152372241)
        ·
          refine ⟨100292407667228644614279181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133723210222971526152372241 100292407667228644614279181)
          ·
            refine ⟨37609652875210741730354693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100292407667228644614279181 37609652875210741730354693)
            ·
              refine ⟨7051809914102014074441505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37609652875210741730354693 7051809914102014074441505)
              ·
                refine ⟨5288857435576510555831129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7051809914102014074441505 5288857435576510555831129)
                ·
                  refine ⟨3966643076682382916873347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5288857435576510555831129 3966643076682382916873347)
                  ·
                    refine ⟨5949964615023574375310021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3966643076682382916873347 5949964615023574375310021)
                    ·
                      refine ⟨1115618365316920195370629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5949964615023574375310021 1115618365316920195370629)
                      ·
                        rfl

theorem cell23_2172659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2, 2, 1, 4].length) (baseStart_2172659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2172659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2172659 prefixEnd_2172659 := by exact prefixLift 2172659
  have htrace : WordTrace (prefixWord ++ tailWord_2172659) baseStart_2172659 baseEnd_2172659 := by
    simpa [prefixWord, tailWord_2172659, baseEnd_2172659] using wordTrace_append hprefix tailTrace_2172659
  have hstable : (prefixWord ++ tailWord_2172659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172659).length < 2 ^ (prefixWord ++ tailWord_2172659).sum := by decide
  have hdescent : baseEnd_2172659 < baseStart_2172659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172660 : List Nat := [2, 6, 1, 1, 1, 2, 1, 4, 5]
def baseStart_2172660 : Nat := 118140960795 + 2172660 * 2 ^ 59
def prefixEnd_2172660 : Nat := 4983230072969 + 3 ^ 40 * 2172660 * 2
def baseEnd_2172660 : Nat := 123957653199730521273125

theorem tailTrace_2172660 : CollatzResearch.WordTrace tailWord_2172660 prefixEnd_2172660 123957653199730521273125 := by
  unfold tailWord_2172660
  simp only [CollatzResearch.WordTrace]
  refine ⟨39621710154415677815725717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52828946872554237087634289 39621710154415677815725717)
  ·
    refine ⟨1857267663488234897612143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 39621710154415677815725717 1857267663488234897612143)
    ·
      refine ⟨2785901495232352346418215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1857267663488234897612143 2785901495232352346418215)
      ·
        refine ⟨4178852242848528519627323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2785901495232352346418215 4178852242848528519627323)
        ·
          refine ⟨6268278364272792779440985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4178852242848528519627323 6268278364272792779440985)
          ·
            refine ⟨4701208773204594584580739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6268278364272792779440985 4701208773204594584580739)
            ·
              refine ⟨7051813159806891876871109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4701208773204594584580739 7051813159806891876871109)
              ·
                refine ⟨1322214967463792226913333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7051813159806891876871109 1322214967463792226913333)
                ·
                  refine ⟨123957653199730521273125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1322214967463792226913333 123957653199730521273125)
                  ·
                    rfl

theorem cell23_2172660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_2172660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2172660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2172660 prefixEnd_2172660 := by exact prefixLift 2172660
  have htrace : WordTrace (prefixWord ++ tailWord_2172660) baseStart_2172660 baseEnd_2172660 := by
    simpa [prefixWord, tailWord_2172660, baseEnd_2172660] using wordTrace_append hprefix tailTrace_2172660
  have hstable : (prefixWord ++ tailWord_2172660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172660).length < 2 ^ (prefixWord ++ tailWord_2172660).sum := by decide
  have hdescent : baseEnd_2172660 < baseStart_2172660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172672 : List Nat := [2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 6]
def baseStart_2172672 : Nat := 118140960795 + 2172672 * 2 ^ 59
def prefixEnd_2172672 : Nat := 4983230072969 + 3 ^ 40 * 2172672 * 2
def baseEnd_2172672 : Nat := 1115625040565428644508069

theorem tailTrace_2172672 : CollatzResearch.WordTrace tailWord_2172672 prefixEnd_2172672 1115625040565428644508069 := by
  unfold tailWord_2172672
  simp only [CollatzResearch.WordTrace]
  refine ⟨39621928992393940840444135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52829238656525254453925513 39621928992393940840444135)
  ·
    refine ⟨59432893488590911260666203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39621928992393940840444135 59432893488590911260666203)
    ·
      refine ⟨89149340232886366890999305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59432893488590911260666203 89149340232886366890999305)
      ·
        refine ⟨66862005174664775168249479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89149340232886366890999305 66862005174664775168249479)
        ·
          refine ⟨100293007761997162752374219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66862005174664775168249479 100293007761997162752374219)
          ·
            refine ⟨150439511642995744128561329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100293007761997162752374219 150439511642995744128561329)
            ·
              refine ⟨112829633732246808096420997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150439511642995744128561329 112829633732246808096420997)
              ·
                refine ⟨21155556324796276518078937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 112829633732246808096420997 21155556324796276518078937)
                ·
                  refine ⟨15866667243597207388559203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21155556324796276518078937 15866667243597207388559203)
                  ·
                    refine ⟨23800000865395811082838805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15866667243597207388559203 23800000865395811082838805)
                    ·
                      refine ⟨1115625040565428644508069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23800000865395811082838805 1115625040565428644508069)
                      ·
                        rfl

theorem cell23_2172672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 6].length) (baseStart_2172672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2172672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2172672 prefixEnd_2172672 := by exact prefixLift 2172672
  have htrace : WordTrace (prefixWord ++ tailWord_2172672) baseStart_2172672 baseEnd_2172672 := by
    simpa [prefixWord, tailWord_2172672, baseEnd_2172672] using wordTrace_append hprefix tailTrace_2172672
  have hstable : (prefixWord ++ tailWord_2172672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172672).length < 2 ^ (prefixWord ++ tailWord_2172672).sum := by decide
  have hdescent : baseEnd_2172672 < baseStart_2172672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172676 : List Nat := [2, 3, 2, 2, 1, 2, 1, 1, 1, 6, 2]
def baseStart_2172676 : Nat := 118140960795 + 2172676 * 2 ^ 59
def prefixEnd_2172676 : Nat := 4983230072969 + 3 ^ 40 * 2172676 * 2
def baseEnd_2172676 : Nat := 1115627094488046628858051

theorem tailTrace_2172676 : CollatzResearch.WordTrace tailWord_2172676 prefixEnd_2172676 1115627094488046628858051 := by
  unfold tailWord_2172676
  simp only [CollatzResearch.WordTrace]
  refine ⟨39622001938386695182016941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52829335917848926909355921 39622001938386695182016941)
  ·
    refine ⟨14858250726895010693256353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39622001938386695182016941 14858250726895010693256353)
    ·
      refine ⟨11143688045171258019942265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14858250726895010693256353 11143688045171258019942265)
      ·
        refine ⟨8357766033878443514956699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11143688045171258019942265 8357766033878443514956699)
        ·
          refine ⟨12536649050817665272435049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8357766033878443514956699 12536649050817665272435049)
          ·
            refine ⟨9402486788113248954326287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12536649050817665272435049 9402486788113248954326287)
            ·
              refine ⟨14103730182169873431489431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9402486788113248954326287 14103730182169873431489431)
              ·
                refine ⟨21155595273254810147234147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14103730182169873431489431 21155595273254810147234147)
                ·
                  refine ⟨31733392909882215220851221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21155595273254810147234147 31733392909882215220851221)
                  ·
                    refine ⟨1487502792650728838477401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 31733392909882215220851221 1487502792650728838477401)
                    ·
                      refine ⟨1115627094488046628858051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1487502792650728838477401 1115627094488046628858051)
                      ·
                        rfl

theorem cell23_2172676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_2172676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2172676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2172676 prefixEnd_2172676 := by exact prefixLift 2172676
  have htrace : WordTrace (prefixWord ++ tailWord_2172676) baseStart_2172676 baseEnd_2172676 := by
    simpa [prefixWord, tailWord_2172676, baseEnd_2172676] using wordTrace_append hprefix tailTrace_2172676
  have hstable : (prefixWord ++ tailWord_2172676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172676).length < 2 ^ (prefixWord ++ tailWord_2172676).sum := by decide
  have hdescent : baseEnd_2172676 < baseStart_2172676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172696 : List Nat := [2, 1, 2, 3, 1, 1, 5, 1, 2, 2, 3]
def baseStart_2172696 : Nat := 118140960795 + 2172696 * 2 ^ 59
def prefixEnd_2172696 : Nat := 4983230072969 + 3 ^ 40 * 2172696 * 2
def baseEnd_2172696 : Nat := 1115637364101136550607959

theorem tailTrace_2172696 : CollatzResearch.WordTrace tailWord_2172696 prefixEnd_2172696 1115637364101136550607959 := by
  unfold tailWord_2172696
  simp only [CollatzResearch.WordTrace]
  refine ⟨39622366668350466889880971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52829822224467289186507961 39622366668350466889880971)
  ·
    refine ⟨59433550002525700334821457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39622366668350466889880971 59433550002525700334821457)
    ·
      refine ⟨44575162501894275251116093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59433550002525700334821457 44575162501894275251116093)
      ·
        refine ⟨16715685938210353219168535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44575162501894275251116093 16715685938210353219168535)
        ·
          refine ⟨25073528907315529828752803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16715685938210353219168535 25073528907315529828752803)
          ·
            refine ⟨37610293360973294743129205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25073528907315529828752803 37610293360973294743129205)
            ·
              refine ⟨3525965002591246382168363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37610293360973294743129205 3525965002591246382168363)
              ·
                refine ⟨5288947503886869573252545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3525965002591246382168363 5288947503886869573252545)
                ·
                  refine ⟨3966710627915152179939409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5288947503886869573252545 3966710627915152179939409)
                  ·
                    refine ⟨2975032970936364134954557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3966710627915152179939409 2975032970936364134954557)
                    ·
                      refine ⟨1115637364101136550607959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2975032970936364134954557 1115637364101136550607959)
                      ·
                        rfl

theorem cell23_2172696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_2172696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2172696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2172696 prefixEnd_2172696 := by exact prefixLift 2172696
  have htrace : WordTrace (prefixWord ++ tailWord_2172696) baseStart_2172696 baseEnd_2172696 := by
    simpa [prefixWord, tailWord_2172696, baseEnd_2172696] using wordTrace_append hprefix tailTrace_2172696
  have hstable : (prefixWord ++ tailWord_2172696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172696).length < 2 ^ (prefixWord ++ tailWord_2172696).sum := by decide
  have hdescent : baseEnd_2172696 < baseStart_2172696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172703 : List Nat := [1, 1, 2, 4, 2, 1, 4, 3, 1, 4]
def baseStart_2172703 : Nat := 118140960795 + 2172703 * 2 ^ 59
def prefixEnd_2172703 : Nat := 4983230072969 + 3 ^ 40 * 2172703 * 2
def baseEnd_2172703 : Nat := 371880319488572674406809

theorem tailTrace_2172703 : CollatzResearch.WordTrace tailWord_2172703 prefixEnd_2172703 371880319488572674406809 := by
  unfold tailWord_2172703
  simp only [CollatzResearch.WordTrace]
  refine ⟨79244988647675573975266763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52829992431783715983511175 79244988647675573975266763)
  ·
    refine ⟨118867482971513360962900145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79244988647675573975266763 118867482971513360962900145)
    ·
      refine ⟨89150612228635020722175109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118867482971513360962900145 89150612228635020722175109)
      ·
        refine ⟨16715739792869066385407833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89150612228635020722175109 16715739792869066385407833)
        ·
          refine ⟨12536804844651799789055875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16715739792869066385407833 12536804844651799789055875)
          ·
            refine ⟨18805207266977699683583813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12536804844651799789055875 18805207266977699683583813)
            ·
              refine ⟨3525976362558318690671965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18805207266977699683583813 3525976362558318690671965)
              ·
                refine ⟨1322241135959369509001987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3525976362558318690671965 1322241135959369509001987)
                ·
                  refine ⟨1983361703939054263502981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1322241135959369509001987 1983361703939054263502981)
                  ·
                    refine ⟨371880319488572674406809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1983361703939054263502981 371880319488572674406809)
                    ·
                      rfl

theorem cell23_2172703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 3, 1, 4].length) (baseStart_2172703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2172703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2172703 prefixEnd_2172703 := by exact prefixLift 2172703
  have htrace : WordTrace (prefixWord ++ tailWord_2172703) baseStart_2172703 baseEnd_2172703 := by
    simpa [prefixWord, tailWord_2172703, baseEnd_2172703] using wordTrace_append hprefix tailTrace_2172703
  have hstable : (prefixWord ++ tailWord_2172703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172703).length < 2 ^ (prefixWord ++ tailWord_2172703).sum := by decide
  have hdescent : baseEnd_2172703 < baseStart_2172703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172716 : List Nat := [2, 2, 1, 1, 1, 7, 1, 2, 6]
def baseStart_2172716 : Nat := 118140960795 + 2172716 * 2 ^ 59
def prefixEnd_2172716 : Nat := 4983230072969 + 3 ^ 40 * 2172716 * 2
def baseEnd_2172716 : Nat := 123960848190469608039763

theorem tailTrace_2172716 : CollatzResearch.WordTrace tailWord_2172716 prefixEnd_2172716 123960848190469608039763 := by
  unfold tailWord_2172716
  simp only [CollatzResearch.WordTrace]
  refine ⟨39622731398314238597745001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52830308531085651463660001 39622731398314238597745001)
  ·
    refine ⟨29717048548735678948308751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39622731398314238597745001 29717048548735678948308751)
    ·
      refine ⟨44575572823103518422463127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29717048548735678948308751 44575572823103518422463127)
      ·
        refine ⟨66863359234655277633694691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44575572823103518422463127 66863359234655277633694691)
        ·
          refine ⟨100295038851982916450542037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66863359234655277633694691 100295038851982916450542037)
          ·
            refine ⟨2350664973093349604309579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 100295038851982916450542037 2350664973093349604309579)
            ·
              refine ⟨3525997459640024406464369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2350664973093349604309579 3525997459640024406464369)
              ·
                refine ⟨2644498094730018304848277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3525997459640024406464369 2644498094730018304848277)
                ·
                  refine ⟨123960848190469608039763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2644498094730018304848277 123960848190469608039763)
                  ·
                    rfl

theorem cell23_2172716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 6].length) (baseStart_2172716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2172716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2172716 prefixEnd_2172716 := by exact prefixLift 2172716
  have htrace : WordTrace (prefixWord ++ tailWord_2172716) baseStart_2172716 baseEnd_2172716 := by
    simpa [prefixWord, tailWord_2172716, baseEnd_2172716] using wordTrace_append hprefix tailTrace_2172716
  have hstable : (prefixWord ++ tailWord_2172716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172716).length < 2 ^ (prefixWord ++ tailWord_2172716).sum := by decide
  have hdescent : baseEnd_2172716 < baseStart_2172716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172733 : List Nat := [1, 4, 1, 4, 1, 2, 3, 1, 6]
def baseStart_2172733 : Nat := 118140960795 + 2172733 * 2 ^ 59
def prefixEnd_2172733 : Nat := 4983230072969 + 3 ^ 40 * 2172733 * 2
def baseEnd_2172733 : Nat := 123961818098372545093921

theorem tailTrace_2172733 : CollatzResearch.WordTrace tailWord_2172733 prefixEnd_2172733 123961818098372545093921 := by
  unfold tailWord_2172733
  simp only [CollatzResearch.WordTrace]
  refine ⟨79246082837566889098858853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52830721891711259399239235 79246082837566889098858853)
  ·
    refine ⟨14858640532043791706036035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79246082837566889098858853 14858640532043791706036035)
    ·
      refine ⟨22287960798065687559054053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14858640532043791706036035 22287960798065687559054053)
      ·
        refine ⟨4178992649637316417322635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22287960798065687559054053 4178992649637316417322635)
        ·
          refine ⟨6268488974455974625983953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4178992649637316417322635 6268488974455974625983953)
          ·
            refine ⟨4701366730841980969487965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6268488974455974625983953 4701366730841980969487965)
            ·
              refine ⟨1763012524065742863557987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4701366730841980969487965 1763012524065742863557987)
              ·
                refine ⟨2644518786098614295336981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1763012524065742863557987 2644518786098614295336981)
                ·
                  refine ⟨123961818098372545093921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2644518786098614295336981 123961818098372545093921)
                  ·
                    rfl

theorem cell23_2172733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 1, 6].length) (baseStart_2172733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2172733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2172733 prefixEnd_2172733 := by exact prefixLift 2172733
  have htrace : WordTrace (prefixWord ++ tailWord_2172733) baseStart_2172733 baseEnd_2172733 := by
    simpa [prefixWord, tailWord_2172733, baseEnd_2172733] using wordTrace_append hprefix tailTrace_2172733
  have hstable : (prefixWord ++ tailWord_2172733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172733).length < 2 ^ (prefixWord ++ tailWord_2172733).sum := by decide
  have hdescent : baseEnd_2172733 < baseStart_2172733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172746 : List Nat := [3, 1, 2, 1, 1, 1, 6, 2, 1, 5]
def baseStart_2172746 : Nat := 118140960795 + 2172746 * 2 ^ 59
def prefixEnd_2172746 : Nat := 4983230072969 + 3 ^ 40 * 2172746 * 2
def baseEnd_2172746 : Nat := 371887679377953784994243

theorem tailTrace_2172746 : CollatzResearch.WordTrace tailWord_2172746 prefixEnd_2172746 371887679377953784994243 := by
  unfold tailWord_2172746
  simp only [CollatzResearch.WordTrace]
  refine ⟨19811639246629948079770523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52831037991013194879388061 19811639246629948079770523)
  ·
    refine ⟨29717458869944922119655785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19811639246629948079770523 29717458869944922119655785)
    ·
      refine ⟨22288094152458691589741839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29717458869944922119655785 22288094152458691589741839)
      ·
        refine ⟨33432141228688037384612759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22288094152458691589741839 33432141228688037384612759)
        ·
          refine ⟨50148211843032056076919139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33432141228688037384612759 50148211843032056076919139)
          ·
            refine ⟨75222317764548084115378709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50148211843032056076919139 75222317764548084115378709)
            ·
              refine ⟨3526046145213191442908377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 75222317764548084115378709 3526046145213191442908377)
              ·
                refine ⟨2644534608909893582181283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3526046145213191442908377 2644534608909893582181283)
                ·
                  refine ⟨3966801913364840373271925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2644534608909893582181283 3966801913364840373271925)
                  ·
                    refine ⟨371887679377953784994243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3966801913364840373271925 371887679377953784994243)
                    ·
                      rfl

theorem cell23_2172746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 2, 1, 5].length) (baseStart_2172746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2172746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2172746 prefixEnd_2172746 := by exact prefixLift 2172746
  have htrace : WordTrace (prefixWord ++ tailWord_2172746) baseStart_2172746 baseEnd_2172746 := by
    simpa [prefixWord, tailWord_2172746, baseEnd_2172746] using wordTrace_append hprefix tailTrace_2172746
  have hstable : (prefixWord ++ tailWord_2172746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172746).length < 2 ^ (prefixWord ++ tailWord_2172746).sum := by decide
  have hdescent : baseEnd_2172746 < baseStart_2172746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172770 : List Nat := [3, 3, 2, 1, 2, 2, 1, 2, 2, 3, 2]
def baseStart_2172770 : Nat := 118140960795 + 2172770 * 2 ^ 59
def prefixEnd_2172770 : Nat := 4983230072969 + 3 ^ 40 * 2172770 * 2
def baseEnd_2172770 : Nat := 1115675361669569261082619

theorem tailTrace_2172770 : CollatzResearch.WordTrace tailWord_2172770 prefixEnd_2172770 1115675361669569261082619 := by
  unfold tailWord_2172770
  simp only [CollatzResearch.WordTrace]
  refine ⟨19811858084608211104488941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52831621558955229611970509 19811858084608211104488941)
  ·
    refine ⟨7429446781728079164183353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19811858084608211104488941 7429446781728079164183353)
    ·
      refine ⟨5572085086296059373137515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7429446781728079164183353 5572085086296059373137515)
      ·
        refine ⟨8358127629444089059706273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5572085086296059373137515 8358127629444089059706273)
        ·
          refine ⟨6268595722083066794779705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8358127629444089059706273 6268595722083066794779705)
          ·
            refine ⟨4701446791562300096084779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6268595722083066794779705 4701446791562300096084779)
            ·
              refine ⟨7052170187343450144127169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4701446791562300096084779 7052170187343450144127169)
              ·
                refine ⟨5289127640507587608095377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7052170187343450144127169 5289127640507587608095377)
                ·
                  refine ⟨3966845730380690706071533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5289127640507587608095377 3966845730380690706071533)
                  ·
                    refine ⟨1487567148892759014776825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3966845730380690706071533 1487567148892759014776825)
                    ·
                      refine ⟨1115675361669569261082619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1487567148892759014776825 1115675361669569261082619)
                      ·
                        rfl

theorem cell23_2172770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_2172770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2172770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2172770 prefixEnd_2172770 := by exact prefixLift 2172770
  have htrace : WordTrace (prefixWord ++ tailWord_2172770) baseStart_2172770 baseEnd_2172770 := by
    simpa [prefixWord, tailWord_2172770, baseEnd_2172770] using wordTrace_append hprefix tailTrace_2172770
  have hstable : (prefixWord ++ tailWord_2172770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172770).length < 2 ^ (prefixWord ++ tailWord_2172770).sum := by decide
  have hdescent : baseEnd_2172770 < baseStart_2172770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172776 : List Nat := [2, 1, 4, 2, 1, 1, 1, 3, 4, 4]
def baseStart_2172776 : Nat := 118140960795 + 2172776 * 2 ^ 59
def prefixEnd_2172776 : Nat := 4983230072969 + 3 ^ 40 * 2172776 * 2
def baseEnd_2172776 : Nat := 371892814184498745869197

theorem tailTrace_2172776 : CollatzResearch.WordTrace tailWord_2172776 prefixEnd_2172776 371892814184498745869197 := by
  unfold tailWord_2172776
  simp only [CollatzResearch.WordTrace]
  refine ⟨39623825588205553721337091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52831767450940738295116121 39623825588205553721337091)
  ·
    refine ⟨59435738382308330582005637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39623825588205553721337091 59435738382308330582005637)
    ·
      refine ⟨11144200946682811984126057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59435738382308330582005637 11144200946682811984126057)
      ·
        refine ⟨8358150710012108988094543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11144200946682811984126057 8358150710012108988094543)
        ·
          refine ⟨12537226065018163482141815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8358150710012108988094543 12537226065018163482141815)
          ·
            refine ⟨18805839097527245223212723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12537226065018163482141815 18805839097527245223212723)
            ·
              refine ⟨28208758646290867834819085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18805839097527245223212723 28208758646290867834819085)
              ·
                refine ⟨10578284492359075438057157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28208758646290867834819085 10578284492359075438057157)
                ·
                  refine ⟨1983428342317326644635717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10578284492359075438057157 1983428342317326644635717)
                  ·
                    refine ⟨371892814184498745869197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1983428342317326644635717 371892814184498745869197)
                    ·
                      rfl

theorem cell23_2172776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_2172776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2172776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2172776 prefixEnd_2172776 := by exact prefixLift 2172776
  have htrace : WordTrace (prefixWord ++ tailWord_2172776) baseStart_2172776 baseEnd_2172776 := by
    simpa [prefixWord, tailWord_2172776, baseEnd_2172776] using wordTrace_append hprefix tailTrace_2172776
  have hstable : (prefixWord ++ tailWord_2172776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172776).length < 2 ^ (prefixWord ++ tailWord_2172776).sum := by decide
  have hdescent : baseEnd_2172776 < baseStart_2172776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172786 : List Nat := [3, 2, 1, 2, 1, 1, 1, 4, 3, 2, 3]
def baseStart_2172786 : Nat := 118140960795 + 2172786 * 2 ^ 59
def prefixEnd_2172786 : Nat := 4983230072969 + 3 ^ 40 * 2172786 * 2
def baseEnd_2172786 : Nat := 1115683577360041198482545

theorem tailTrace_2172786 : CollatzResearch.WordTrace tailWord_2172786 prefixEnd_2172786 1115683577360041198482545 := by
  unfold tailWord_2172786
  simp only [CollatzResearch.WordTrace]
  refine ⟨19812003976593719787634553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52832010604249919433692141 19812003976593719787634553)
  ·
    refine ⟨14859002982445289840725915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19812003976593719787634553 14859002982445289840725915)
    ·
      refine ⟨22288504473667934761088873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14859002982445289840725915 22288504473667934761088873)
      ·
        refine ⟨16716378355250951070816655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22288504473667934761088873 16716378355250951070816655)
        ·
          refine ⟨25074567532876426606224983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16716378355250951070816655 25074567532876426606224983)
          ·
            refine ⟨37611851299314639909337475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25074567532876426606224983 37611851299314639909337475)
            ·
              refine ⟨56417776948971959864006213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37611851299314639909337475 56417776948971959864006213)
              ·
                refine ⟨10578333177932242474501165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56417776948971959864006213 10578333177932242474501165)
                ·
                  refine ⟨3966874941724590927937937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10578333177932242474501165 3966874941724590927937937)
                  ·
                    refine ⟨2975156206293443195953453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3966874941724590927937937 2975156206293443195953453)
                    ·
                      refine ⟨1115683577360041198482545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2975156206293443195953453 1115683577360041198482545)
                      ·
                        rfl

theorem cell23_2172786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_2172786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2172786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2172786 prefixEnd_2172786 := by exact prefixLift 2172786
  have htrace : WordTrace (prefixWord ++ tailWord_2172786) baseStart_2172786 baseEnd_2172786 := by
    simpa [prefixWord, tailWord_2172786, baseEnd_2172786] using wordTrace_append hprefix tailTrace_2172786
  have hstable : (prefixWord ++ tailWord_2172786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172786).length < 2 ^ (prefixWord ++ tailWord_2172786).sum := by decide
  have hdescent : baseEnd_2172786 < baseStart_2172786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172803 : List Nat := [1, 1, 1, 3, 4, 2, 3, 2, 1, 2, 3]
def baseStart_2172803 : Nat := 118140960795 + 2172803 * 2 ^ 59
def prefixEnd_2172803 : Nat := 4983230072969 + 3 ^ 40 * 2172803 * 2
def baseEnd_2172803 : Nat := 1115692306531167631969967

theorem tailTrace_2172803 : CollatzResearch.WordTrace tailWord_2172803 prefixEnd_2172803 1115692306531167631969967 := by
  unfold tailWord_2172803
  simp only [CollatzResearch.WordTrace]
  refine ⟨79248635947313291053907063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52832423964875527369271375 79248635947313291053907063)
  ·
    refine ⟨118872953920969936580860595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79248635947313291053907063 118872953920969936580860595)
    ·
      refine ⟨178309430881454904871290893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118872953920969936580860595 178309430881454904871290893)
      ·
        refine ⟨66866036580545589326734085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 178309430881454904871290893 66866036580545589326734085)
        ·
          refine ⟨12537381858852297998762641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66866036580545589326734085 12537381858852297998762641)
          ·
            refine ⟨9403036394139223499071981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12537381858852297998762641 9403036394139223499071981)
            ·
              refine ⟨3526138647802208812151993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9403036394139223499071981 3526138647802208812151993)
              ·
                refine ⟨2644603985851656609113995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3526138647802208812151993 2644603985851656609113995)
                ·
                  refine ⟨3966905978777484913670993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2644603985851656609113995 3966905978777484913670993)
                  ·
                    refine ⟨2975179484083113685253245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3966905978777484913670993 2975179484083113685253245)
                    ·
                      refine ⟨1115692306531167631969967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2975179484083113685253245 1115692306531167631969967)
                      ·
                        rfl

theorem cell23_2172803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 2, 1, 2, 3].length) (baseStart_2172803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2172803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2172803 prefixEnd_2172803 := by exact prefixLift 2172803
  have htrace : WordTrace (prefixWord ++ tailWord_2172803) baseStart_2172803 baseEnd_2172803 := by
    simpa [prefixWord, tailWord_2172803, baseEnd_2172803] using wordTrace_append hprefix tailTrace_2172803
  have hstable : (prefixWord ++ tailWord_2172803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172803).length < 2 ^ (prefixWord ++ tailWord_2172803).sum := by decide
  have hdescent : baseEnd_2172803 < baseStart_2172803 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172834 : List Nat := [3, 3, 1, 2, 3, 1, 1, 4, 1, 2, 2]
def baseStart_2172834 : Nat := 118140960795 + 2172834 * 2 ^ 59
def prefixEnd_2172834 : Nat := 4983230072969 + 3 ^ 40 * 2172834 * 2
def baseEnd_2172834 : Nat := 1115708224431457010682325

theorem tailTrace_2172834 : CollatzResearch.WordTrace tailWord_2172834 prefixEnd_2172834 1115708224431457010682325 := by
  unfold tailWord_2172834
  simp only [CollatzResearch.WordTrace]
  refine ⟨19812441652550245837071389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52833177740133988898857037 19812441652550245837071389)
  ·
    refine ⟨7429665619706342188901771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19812441652550245837071389 7429665619706342188901771)
    ·
      refine ⟨11144498429559513283352657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7429665619706342188901771 11144498429559513283352657)
      ·
        refine ⟨8358373822169634962514493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11144498429559513283352657 8358373822169634962514493)
        ·
          refine ⟨3134390183313613110942935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8358373822169634962514493 3134390183313613110942935)
          ·
            refine ⟨4701585274970419666414403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3134390183313613110942935 4701585274970419666414403)
            ·
              refine ⟨7052377912455629499621605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4701585274970419666414403 7052377912455629499621605)
              ·
                refine ⟨1322320858585430531179051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7052377912455629499621605 1322320858585430531179051)
                ·
                  refine ⟨1983481287878145796768577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1322320858585430531179051 1983481287878145796768577)
                  ·
                    refine ⟨1487610965908609347576433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1983481287878145796768577 1487610965908609347576433)
                    ·
                      refine ⟨1115708224431457010682325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1487610965908609347576433 1115708224431457010682325)
                      ·
                        rfl

theorem cell23_2172834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_2172834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2172834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2172834 prefixEnd_2172834 := by exact prefixLift 2172834
  have htrace : WordTrace (prefixWord ++ tailWord_2172834) baseStart_2172834 baseEnd_2172834 := by
    simpa [prefixWord, tailWord_2172834, baseEnd_2172834] using wordTrace_append hprefix tailTrace_2172834
  have hstable : (prefixWord ++ tailWord_2172834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172834).length < 2 ^ (prefixWord ++ tailWord_2172834).sum := by decide
  have hdescent : baseEnd_2172834 < baseStart_2172834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172840 : List Nat := [2, 1, 6, 2, 1, 2, 1, 8]
def baseStart_2172840 : Nat := 118140960795 + 2172840 * 2 ^ 59
def prefixEnd_2172840 : Nat := 4983230072969 + 3 ^ 40 * 2172840 * 2
def baseEnd_2172840 : Nat := 41322640937606814341011

theorem tailTrace_2172840 : CollatzResearch.WordTrace tailWord_2172840 prefixEnd_2172840 41322640937606814341011 := by
  unfold tailWord_2172840
  simp only [CollatzResearch.WordTrace]
  refine ⟨39624992724089623186501987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52833323632119497582002649 39624992724089623186501987)
  ·
    refine ⟨59437489086134434779752981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39624992724089623186501987 59437489086134434779752981)
    ·
      refine ⟨2786132300912551630300921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 59437489086134434779752981 2786132300912551630300921)
      ·
        refine ⟨2089599225684413722725691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2786132300912551630300921 2089599225684413722725691)
        ·
          refine ⟨3134398838526620584088537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2089599225684413722725691 3134398838526620584088537)
          ·
            refine ⟨2350799128894965438066403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3134398838526620584088537 2350799128894965438066403)
            ·
              refine ⟨3526198693342448157099605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2350799128894965438066403 3526198693342448157099605)
              ·
                refine ⟨41322640937606814341011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3526198693342448157099605 41322640937606814341011)
                ·
                  rfl

theorem cell23_2172840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 8].length) (baseStart_2172840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2172840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2172840 prefixEnd_2172840 := by exact prefixLift 2172840
  have htrace : WordTrace (prefixWord ++ tailWord_2172840) baseStart_2172840 baseEnd_2172840 := by
    simpa [prefixWord, tailWord_2172840, baseEnd_2172840] using wordTrace_append hprefix tailTrace_2172840
  have hstable : (prefixWord ++ tailWord_2172840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172840).length < 2 ^ (prefixWord ++ tailWord_2172840).sum := by decide
  have hdescent : baseEnd_2172840 < baseStart_2172840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172873 : List Nat := [1, 2, 1, 1, 2, 1, 2, 3, 6, 2, 2]
def baseStart_2172873 : Nat := 118140960795 + 2172873 * 2 ^ 59
def prefixEnd_2172873 : Nat := 4983230072969 + 3 ^ 40 * 2172873 * 2
def baseEnd_2172873 : Nat := 1115728250176982358094645

theorem tailTrace_2172873 : CollatzResearch.WordTrace tailWord_2172873 prefixEnd_2172873 1115728250176982358094645 := by
  unfold tailWord_2172873
  simp only [CollatzResearch.WordTrace]
  refine ⟨79251189057059693008955273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52834126038039795339303515 79251189057059693008955273)
  ·
    refine ⟨59438391792794769756716455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79251189057059693008955273 59438391792794769756716455)
    ·
      refine ⟨89157587689192154635074683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59438391792794769756716455 89157587689192154635074683)
      ·
        refine ⟨133736381533788231952612025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89157587689192154635074683 133736381533788231952612025)
        ·
          refine ⟨100302286150341173964459019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133736381533788231952612025 100302286150341173964459019)
          ·
            refine ⟨150453429225511760946688529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100302286150341173964459019 150453429225511760946688529)
            ·
              refine ⟨112840071919133820710016397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150453429225511760946688529 112840071919133820710016397)
              ·
                refine ⟨42315026969675182766256149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 112840071919133820710016397 42315026969675182766256149)
                ·
                  refine ⟨1983516889203524192168257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 42315026969675182766256149 1983516889203524192168257)
                  ·
                    refine ⟨1487637666902643144126193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1983516889203524192168257 1487637666902643144126193)
                    ·
                      refine ⟨1115728250176982358094645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1487637666902643144126193 1115728250176982358094645)
                      ·
                        rfl

theorem cell23_2172873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 6, 2, 2].length) (baseStart_2172873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2172873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2172873 prefixEnd_2172873 := by exact prefixLift 2172873
  have htrace : WordTrace (prefixWord ++ tailWord_2172873) baseStart_2172873 baseEnd_2172873 := by
    simpa [prefixWord, tailWord_2172873, baseEnd_2172873] using wordTrace_append hprefix tailTrace_2172873
  have hstable : (prefixWord ++ tailWord_2172873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172873).length < 2 ^ (prefixWord ++ tailWord_2172873).sum := by decide
  have hdescent : baseEnd_2172873 < baseStart_2172873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172879 : List Nat := [1, 1, 2, 1, 1, 5, 1, 2, 9]
def baseStart_2172879 : Nat := 118140960795 + 2172879 * 2 ^ 59
def prefixEnd_2172879 : Nat := 4983230072969 + 3 ^ 40 * 2172879 * 2
def baseEnd_2172879 : Nat := 123970147895656592735513

theorem tailTrace_2172879 : CollatzResearch.WordTrace tailWord_2172879 prefixEnd_2172879 123970147895656592735513 := by
  unfold tailWord_2172879
  simp only [CollatzResearch.WordTrace]
  refine ⟨79251407895037956033673691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52834271930025304022449127 79251407895037956033673691)
  ·
    refine ⟨118877111842556934050510537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79251407895037956033673691 118877111842556934050510537)
    ·
      refine ⟨89157833881917700537882903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118877111842556934050510537 89157833881917700537882903)
      ·
        refine ⟨133736750822876550806824355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89157833881917700537882903 133736750822876550806824355)
        ·
          refine ⟨200605126234314826210236533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133736750822876550806824355 200605126234314826210236533)
          ·
            refine ⟨18806730584467014957209675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 200605126234314826210236533 18806730584467014957209675)
            ·
              refine ⟨28210095876700522435814513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18806730584467014957209675 28210095876700522435814513)
              ·
                refine ⟨21157571907525391826860885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28210095876700522435814513 21157571907525391826860885)
                ·
                  refine ⟨123970147895656592735513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 21157571907525391826860885 123970147895656592735513)
                  ·
                    rfl

theorem cell23_2172879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 9].length) (baseStart_2172879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2172879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2172879 prefixEnd_2172879 := by exact prefixLift 2172879
  have htrace : WordTrace (prefixWord ++ tailWord_2172879) baseStart_2172879 baseEnd_2172879 := by
    simpa [prefixWord, tailWord_2172879, baseEnd_2172879] using wordTrace_append hprefix tailTrace_2172879
  have hstable : (prefixWord ++ tailWord_2172879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172879).length < 2 ^ (prefixWord ++ tailWord_2172879).sum := by decide
  have hdescent : baseEnd_2172879 < baseStart_2172879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172936 : List Nat := [2, 1, 3, 2, 1, 2, 2, 2, 1, 2, 5]
def baseStart_2172936 : Nat := 118140960795 + 2172936 * 2 ^ 59
def prefixEnd_2172936 : Nat := 4983230072969 + 3 ^ 40 * 2172936 * 2
def baseEnd_2172936 : Nat := 1115760599458215611606855

theorem tailTrace_2172936 : CollatzResearch.WordTrace tailWord_2172936 prefixEnd_2172936 1115760599458215611606855 := by
  unfold tailWord_2172936
  simp only [CollatzResearch.WordTrace]
  refine ⟨39626743427915727384249331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52835657903887636512332441 39626743427915727384249331)
  ·
    refine ⟨59440115141873591076373997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39626743427915727384249331 59440115141873591076373997)
    ·
      refine ⟨22290043178202596653640249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59440115141873591076373997 22290043178202596653640249)
      ·
        refine ⟨16717532383651947490230187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22290043178202596653640249 16717532383651947490230187)
        ·
          refine ⟨25076298575477921235345281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16717532383651947490230187 25076298575477921235345281)
          ·
            refine ⟨18807223931608440926508961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25076298575477921235345281 18807223931608440926508961)
            ·
              refine ⟨14105417948706330694881721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18807223931608440926508961 14105417948706330694881721)
              ·
                refine ⟨10579063461529748021161291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14105417948706330694881721 10579063461529748021161291)
                ·
                  refine ⟨15868595192294622031741937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10579063461529748021161291 15868595192294622031741937)
                  ·
                    refine ⟨11901446394220966523806453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15868595192294622031741937 11901446394220966523806453)
                    ·
                      refine ⟨1115760599458215611606855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11901446394220966523806453 1115760599458215611606855)
                      ·
                        rfl

theorem cell23_2172936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_2172936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2172936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2172936 prefixEnd_2172936 := by exact prefixLift 2172936
  have htrace : WordTrace (prefixWord ++ tailWord_2172936) baseStart_2172936 baseEnd_2172936 := by
    simpa [prefixWord, tailWord_2172936, baseEnd_2172936] using wordTrace_append hprefix tailTrace_2172936
  have hstable : (prefixWord ++ tailWord_2172936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172936).length < 2 ^ (prefixWord ++ tailWord_2172936).sum := by decide
  have hdescent : baseEnd_2172936 < baseStart_2172936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172963 : List Nat := [1, 1, 1, 4, 3, 1, 2, 1, 1, 6, 2]
def baseStart_2172963 : Nat := 118140960795 + 2172963 * 2 ^ 59
def prefixEnd_2172963 : Nat := 4983230072969 + 3 ^ 40 * 2172963 * 2
def baseEnd_2172963 : Nat := 1115774463435887005969231

theorem tailTrace_2172963 : CollatzResearch.WordTrace tailWord_2172963 prefixEnd_2172963 1115774463435887005969231 := by
  unfold tailWord_2172963
  simp only [CollatzResearch.WordTrace]
  refine ⟨79254471626733638379731543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52836314417822425586487695 79254471626733638379731543)
  ·
    refine ⟨118881707440100457569597315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79254471626733638379731543 118881707440100457569597315)
    ·
      refine ⟨178322561160150686354395973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118881707440100457569597315 178322561160150686354395973)
      ·
        refine ⟨33435480217528253691449245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 178322561160150686354395973 33435480217528253691449245)
        ·
          refine ⟨12538305081573095134293467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33435480217528253691449245 12538305081573095134293467)
          ·
            refine ⟨18807457622359642701440201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12538305081573095134293467 18807457622359642701440201)
            ·
              refine ⟨14105593216769732026080151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18807457622359642701440201 14105593216769732026080151)
              ·
                refine ⟨21158389825154598039120227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14105593216769732026080151 21158389825154598039120227)
                ·
                  refine ⟨31737584737731897058680341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21158389825154598039120227 31737584737731897058680341)
                  ·
                    refine ⟨1487699284581182674625641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 31737584737731897058680341 1487699284581182674625641)
                    ·
                      refine ⟨1115774463435887005969231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1487699284581182674625641 1115774463435887005969231)
                      ·
                        rfl

theorem cell23_2172963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 6, 2].length) (baseStart_2172963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2172963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2172963 prefixEnd_2172963 := by exact prefixLift 2172963
  have htrace : WordTrace (prefixWord ++ tailWord_2172963) baseStart_2172963 baseEnd_2172963 := by
    simpa [prefixWord, tailWord_2172963, baseEnd_2172963] using wordTrace_append hprefix tailTrace_2172963
  have hstable : (prefixWord ++ tailWord_2172963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172963).length < 2 ^ (prefixWord ++ tailWord_2172963).sum := by decide
  have hdescent : baseEnd_2172963 < baseStart_2172963 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172983 : List Nat := [1, 1, 3, 1, 2, 2, 3, 3, 2, 2, 3]
def baseStart_2172983 : Nat := 118140960795 + 2172983 * 2 ^ 59
def prefixEnd_2172983 : Nat := 4983230072969 + 3 ^ 40 * 2172983 * 2
def baseEnd_2172983 : Nat := 1115784733048976927719139

theorem tailTrace_2172983 : CollatzResearch.WordTrace tailWord_2172983 prefixEnd_2172983 1115784733048976927719139 := by
  unfold tailWord_2172983
  simp only [CollatzResearch.WordTrace]
  refine ⟨79255201086661181795459603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52836800724440787863639735 79255201086661181795459603)
  ·
    refine ⟨118882801629991772693189405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79255201086661181795459603 118882801629991772693189405)
    ·
      refine ⟨44581050611246914759946027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118882801629991772693189405 44581050611246914759946027)
      ·
        refine ⟨66871575916870372139919041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44581050611246914759946027 66871575916870372139919041)
        ·
          refine ⟨50153681937652779104939281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66871575916870372139919041 50153681937652779104939281)
          ·
            refine ⟨37615261453239584328704461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50153681937652779104939281 37615261453239584328704461)
            ·
              refine ⟨14105723044964844123264173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37615261453239584328704461 14105723044964844123264173)
              ·
                refine ⟨5289646141861816546224065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14105723044964844123264173 5289646141861816546224065)
                ·
                  refine ⟨3967234606396362409668049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5289646141861816546224065 3967234606396362409668049)
                  ·
                    refine ⟨2975425954797271807251037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3967234606396362409668049 2975425954797271807251037)
                    ·
                      refine ⟨1115784733048976927719139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2975425954797271807251037 1115784733048976927719139)
                      ·
                        rfl

theorem cell23_2172983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3, 2, 2, 3].length) (baseStart_2172983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2172983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2172983 prefixEnd_2172983 := by exact prefixLift 2172983
  have htrace : WordTrace (prefixWord ++ tailWord_2172983) baseStart_2172983 baseEnd_2172983 := by
    simpa [prefixWord, tailWord_2172983, baseEnd_2172983] using wordTrace_append hprefix tailTrace_2172983
  have hstable : (prefixWord ++ tailWord_2172983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172983).length < 2 ^ (prefixWord ++ tailWord_2172983).sum := by decide
  have hdescent : baseEnd_2172983 < baseStart_2172983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173014 : List Nat := [5, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2]
def baseStart_2173014 : Nat := 118140960795 + 2173014 * 2 ^ 59
def prefixEnd_2173014 : Nat := 4983230072969 + 3 ^ 40 * 2173014 * 2
def baseEnd_2173014 : Nat := 1115800650949266306431497

theorem tailTrace_2173014 : CollatzResearch.WordTrace tailWord_2173014 prefixEnd_2173014 1115800650949266306431497 := by
  unfold tailWord_2173014
  simp only [CollatzResearch.WordTrace]
  refine ⟨4953520734346804630614881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52837554499699249393225397 4953520734346804630614881)
  ·
    refine ⟨3715140550760103472961161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4953520734346804630614881 3715140550760103472961161)
    ·
      refine ⟨2786355413070077604720871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3715140550760103472961161 2786355413070077604720871)
      ·
        refine ⟨4179533119605116407081307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2786355413070077604720871 4179533119605116407081307)
        ·
          refine ⟨6269299679407674610621961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4179533119605116407081307 6269299679407674610621961)
          ·
            refine ⟨4701974759555755957966471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6269299679407674610621961 4701974759555755957966471)
            ·
              refine ⟨7052962139333633936949707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4701974759555755957966471 7052962139333633936949707)
              ·
                refine ⟨10579443209000450905424561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7052962139333633936949707 10579443209000450905424561)
                ·
                  refine ⟨7934582406750338179068421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10579443209000450905424561 7934582406750338179068421)
                  ·
                    refine ⟨1487734201265688408575329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7934582406750338179068421 1487734201265688408575329)
                    ·
                      refine ⟨1115800650949266306431497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1487734201265688408575329 1115800650949266306431497)
                      ·
                        rfl

theorem cell23_2173014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_2173014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2173014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2173014 prefixEnd_2173014 := by exact prefixLift 2173014
  have htrace : WordTrace (prefixWord ++ tailWord_2173014) baseStart_2173014 baseEnd_2173014 := by
    simpa [prefixWord, tailWord_2173014, baseEnd_2173014] using wordTrace_append hprefix tailTrace_2173014
  have hstable : (prefixWord ++ tailWord_2173014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173014).length < 2 ^ (prefixWord ++ tailWord_2173014).sum := by decide
  have hdescent : baseEnd_2173014 < baseStart_2173014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173033 : List Nat := [1, 2, 1, 1, 1, 5, 2, 4, 1, 5]
def baseStart_2173033 : Nat := 118140960795 + 2173033 * 2 ^ 59
def prefixEnd_2173033 : Nat := 4983230072969 + 3 ^ 40 * 2173033 * 2
def baseEnd_2173033 : Nat := 371936802360567244031303

theorem tailTrace_2173033 : CollatzResearch.WordTrace tailWord_2173033 prefixEnd_2173033 371936802360567244031303 := by
  unfold tailWord_2173033
  simp only [CollatzResearch.WordTrace]
  refine ⟨79257024736480040334779753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52838016490986693556519835 79257024736480040334779753)
  ·
    refine ⟨59442768552360030251084815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79257024736480040334779753 59442768552360030251084815)
    ·
      refine ⟨89164152828540045376627223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59442768552360030251084815 89164152828540045376627223)
      ·
        refine ⟨133746229242810068064940835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89164152828540045376627223 133746229242810068064940835)
        ·
          refine ⟨200619343864215102097411253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133746229242810068064940835 200619343864215102097411253)
          ·
            refine ⟨18808063487270165821632305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 200619343864215102097411253 18808063487270165821632305)
            ·
              refine ⟨14106047615452624366224229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18808063487270165821632305 14106047615452624366224229)
              ·
                refine ⟨2644883927897367068667043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14106047615452624366224229 2644883927897367068667043)
                ·
                  refine ⟨3967325891846050603000565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2644883927897367068667043 3967325891846050603000565)
                  ·
                    refine ⟨371936802360567244031303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3967325891846050603000565 371936802360567244031303)
                    ·
                      rfl

theorem cell23_2173033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 4, 1, 5].length) (baseStart_2173033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2173033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2173033 prefixEnd_2173033 := by exact prefixLift 2173033
  have htrace : WordTrace (prefixWord ++ tailWord_2173033) baseStart_2173033 baseEnd_2173033 := by
    simpa [prefixWord, tailWord_2173033, baseEnd_2173033] using wordTrace_append hprefix tailTrace_2173033
  have hstable : (prefixWord ++ tailWord_2173033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173033).length < 2 ^ (prefixWord ++ tailWord_2173033).sum := by decide
  have hdescent : baseEnd_2173033 < baseStart_2173033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173034 : List Nat := [3, 1, 3, 2, 4, 1, 1, 1, 2, 2, 3]
def baseStart_2173034 : Nat := 118140960795 + 2173034 * 2 ^ 59
def prefixEnd_2173034 : Nat := 4983230072969 + 3 ^ 40 * 2173034 * 2
def baseEnd_2173034 : Nat := 1115810920562356228181405

theorem tailTrace_2173034 : CollatzResearch.WordTrace tailWord_2173034 prefixEnd_2173034 1115810920562356228181405 := by
  unfold tailWord_2173034
  simp only [CollatzResearch.WordTrace]
  refine ⟨19814265302369104376391539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52838040806317611670377437 19814265302369104376391539)
  ·
    refine ⟨29721397953553656564587309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19814265302369104376391539 29721397953553656564587309)
    ·
      refine ⟨11145524232582621211720241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29721397953553656564587309 11145524232582621211720241)
      ·
        refine ⟨8359143174436965908790181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11145524232582621211720241 8359143174436965908790181)
        ·
          refine ⟨1567339345206931107898159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8359143174436965908790181 1567339345206931107898159)
          ·
            refine ⟨2351009017810396661847239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1567339345206931107898159 2351009017810396661847239)
            ·
              refine ⟨3526513526715594992770859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2351009017810396661847239 3526513526715594992770859)
              ·
                refine ⟨5289770290073392489156289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3526513526715594992770859 5289770290073392489156289)
                ·
                  refine ⟨3967327717555044366867217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5289770290073392489156289 3967327717555044366867217)
                  ·
                    refine ⟨2975495788166283275150413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3967327717555044366867217 2975495788166283275150413)
                    ·
                      refine ⟨1115810920562356228181405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2975495788166283275150413 1115810920562356228181405)
                      ·
                        rfl

theorem cell23_2173034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_2173034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2173034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2173034 prefixEnd_2173034 := by exact prefixLift 2173034
  have htrace : WordTrace (prefixWord ++ tailWord_2173034) baseStart_2173034 baseEnd_2173034 := by
    simpa [prefixWord, tailWord_2173034, baseEnd_2173034] using wordTrace_append hprefix tailTrace_2173034
  have hstable : (prefixWord ++ tailWord_2173034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173034).length < 2 ^ (prefixWord ++ tailWord_2173034).sum := by decide
  have hdescent : baseEnd_2173034 < baseStart_2173034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173040 : List Nat := [2, 1, 1, 1, 5, 3, 1, 1, 1, 5, 2]
def baseStart_2173040 : Nat := 118140960795 + 2173040 * 2 ^ 59
def prefixEnd_2173040 : Nat := 4983230072969 + 3 ^ 40 * 2173040 * 2
def baseEnd_2173040 : Nat := 1115814001446283204706377

theorem tailTrace_2173040 : CollatzResearch.WordTrace tailWord_2173040 prefixEnd_2173040 1115814001446283204706377 := by
  unfold tailWord_2173040
  simp only [CollatzResearch.WordTrace]
  refine ⟨39628640023727340265142287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52838186698303120353523049 39628640023727340265142287)
  ·
    refine ⟨59442960035591010397713431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39628640023727340265142287 59442960035591010397713431)
    ·
      refine ⟨89164440053386515596570147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59442960035591010397713431 89164440053386515596570147)
      ·
        refine ⟨133746660080079773394855221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89164440053386515596570147 133746660080079773394855221)
        ·
          refine ⟨12538749382507478755767677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 133746660080079773394855221 12538749382507478755767677)
          ·
            refine ⟨4702031018440304533412879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12538749382507478755767677 4702031018440304533412879)
            ·
              refine ⟨7053046527660456800119319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4702031018440304533412879 7053046527660456800119319)
              ·
                refine ⟨10579569791490685200178979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7053046527660456800119319 10579569791490685200178979)
                ·
                  refine ⟨15869354687236027800268469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10579569791490685200178979 15869354687236027800268469)
                  ·
                    refine ⟨1487752001928377606275169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15869354687236027800268469 1487752001928377606275169)
                    ·
                      refine ⟨1115814001446283204706377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1487752001928377606275169 1115814001446283204706377)
                      ·
                        rfl

theorem cell23_2173040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 1, 5, 2].length) (baseStart_2173040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2173040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2173040 prefixEnd_2173040 := by exact prefixLift 2173040
  have htrace : WordTrace (prefixWord ++ tailWord_2173040) baseStart_2173040 baseEnd_2173040 := by
    simpa [prefixWord, tailWord_2173040, baseEnd_2173040] using wordTrace_append hprefix tailTrace_2173040
  have hstable : (prefixWord ++ tailWord_2173040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173040).length < 2 ^ (prefixWord ++ tailWord_2173040).sum := by decide
  have hdescent : baseEnd_2173040 < baseStart_2173040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173047 : List Nat := [1, 1, 3, 1, 1, 5, 1, 5, 1, 1, 3]
def baseStart_2173047 : Nat := 118140960795 + 2173047 * 2 ^ 59
def prefixEnd_2173047 : Nat := 4983230072969 + 3 ^ 40 * 2173047 * 2
def baseEnd_2173047 : Nat := 1115817595810864677318845

theorem tailTrace_2173047 : CollatzResearch.WordTrace tailWord_2173047 prefixEnd_2173047 1115817595810864677318845 := by
  unfold tailWord_2173047
  simp only [CollatzResearch.WordTrace]
  refine ⟨79257535358429320725789395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52838356905619547150526263 79257535358429320725789395)
  ·
    refine ⟨118886303037643981088684093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79257535358429320725789395 118886303037643981088684093)
    ·
      refine ⟨44582363639116492908256535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118886303037643981088684093 44582363639116492908256535)
      ·
        refine ⟨66873545458674739362384803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44582363639116492908256535 66873545458674739362384803)
        ·
          refine ⟨100310318188012109043577205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66873545458674739362384803 100310318188012109043577205)
          ·
            refine ⟨9404092330126135222835363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 100310318188012109043577205 9404092330126135222835363)
            ·
              refine ⟨14106138495189202834253045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9404092330126135222835363 14106138495189202834253045)
              ·
                refine ⟨1322450483923987765711223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14106138495189202834253045 1322450483923987765711223)
                ·
                  refine ⟨1983675725885981648566835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1322450483923987765711223 1983675725885981648566835)
                  ·
                    refine ⟨2975513588828972472850253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1983675725885981648566835 2975513588828972472850253)
                    ·
                      refine ⟨1115817595810864677318845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2975513588828972472850253 1115817595810864677318845)
                      ·
                        rfl

theorem cell23_2173047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 5, 1, 1, 3].length) (baseStart_2173047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2173047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2173047 prefixEnd_2173047 := by exact prefixLift 2173047
  have htrace : WordTrace (prefixWord ++ tailWord_2173047) baseStart_2173047 baseEnd_2173047 := by
    simpa [prefixWord, tailWord_2173047, baseEnd_2173047] using wordTrace_append hprefix tailTrace_2173047
  have hstable : (prefixWord ++ tailWord_2173047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173047).length < 2 ^ (prefixWord ++ tailWord_2173047).sum := by decide
  have hdescent : baseEnd_2173047 < baseStart_2173047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173064 : List Nat := [2, 1, 3, 4, 1, 1, 2, 4, 1, 1, 3]
def baseStart_2173064 : Nat := 118140960795 + 2173064 * 2 ^ 59
def prefixEnd_2173064 : Nat := 4983230072969 + 3 ^ 40 * 2173064 * 2
def baseEnd_2173064 : Nat := 1115826324981991110806267

theorem tailTrace_2173064 : CollatzResearch.WordTrace tailWord_2173064 prefixEnd_2173064 1115826324981991110806267 := by
  unfold tailWord_2173064
  simp only [CollatzResearch.WordTrace]
  refine ⟨39629077699683866314579123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52838770266245155086105497 39629077699683866314579123)
  ·
    refine ⟨59443616549525799471868685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39629077699683866314579123 59443616549525799471868685)
    ·
      refine ⟨22291356206072174801950757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59443616549525799471868685 22291356206072174801950757)
      ·
        refine ⟨4179629288638532775365767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22291356206072174801950757 4179629288638532775365767)
        ·
          refine ⟨6269443932957799163048651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4179629288638532775365767 6269443932957799163048651)
          ·
            refine ⟨9404165899436698744572977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6269443932957799163048651 9404165899436698744572977)
            ·
              refine ⟨7053124424577524058429733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9404165899436698744572977 7053124424577524058429733)
              ·
                refine ⟨1322460829608285760955575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7053124424577524058429733 1322460829608285760955575)
                ·
                  refine ⟨1983691244412428641433363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1322460829608285760955575 1983691244412428641433363)
                  ·
                    refine ⟨2975536866618642962150045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1983691244412428641433363 2975536866618642962150045)
                    ·
                      refine ⟨1115826324981991110806267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2975536866618642962150045 1115826324981991110806267)
                      ·
                        rfl

theorem cell23_2173064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_2173064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2173064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2173064 prefixEnd_2173064 := by exact prefixLift 2173064
  have htrace : WordTrace (prefixWord ++ tailWord_2173064) baseStart_2173064 baseEnd_2173064 := by
    simpa [prefixWord, tailWord_2173064, baseEnd_2173064] using wordTrace_append hprefix tailTrace_2173064
  have hstable : (prefixWord ++ tailWord_2173064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173064).length < 2 ^ (prefixWord ++ tailWord_2173064).sum := by decide
  have hdescent : baseEnd_2173064 < baseStart_2173064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173087 : List Nat := [1, 1, 2, 6, 1, 2, 2, 2, 1, 1, 4]
def baseStart_2173087 : Nat := 118140960795 + 2173087 * 2 ^ 59
def prefixEnd_2173087 : Nat := 4983230072969 + 3 ^ 40 * 2173087 * 2
def baseEnd_2173087 : Nat := 1115838135037044520818661

theorem tailTrace_2173087 : CollatzResearch.WordTrace tailWord_2173087 prefixEnd_2173087 1115838135037044520818661 := by
  unfold tailWord_2173087
  simp only [CollatzResearch.WordTrace]
  refine ⟨79258994278284407557245515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52839329518856271704830343 79258994278284407557245515)
  ·
    refine ⟨118888491417426611335868273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79258994278284407557245515 118888491417426611335868273)
    ·
      refine ⟨89166368563069958501901205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118888491417426611335868273 89166368563069958501901205)
      ·
        refine ⟨4179673526393904304776619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 89166368563069958501901205 4179673526393904304776619)
        ·
          refine ⟨6269510289590856457164929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4179673526393904304776619 6269510289590856457164929)
          ·
            refine ⟨4702132717193142342873697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6269510289590856457164929 4702132717193142342873697)
            ·
              refine ⟨3526599537894856757155273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4702132717193142342873697 3526599537894856757155273)
              ·
                refine ⟨2644949653421142567866455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3526599537894856757155273 2644949653421142567866455)
                ·
                  refine ⟨3967424480131713851799683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2644949653421142567866455 3967424480131713851799683)
                  ·
                    refine ⟨5951136720197570777699525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3967424480131713851799683 5951136720197570777699525)
                    ·
                      refine ⟨1115838135037044520818661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5951136720197570777699525 1115838135037044520818661)
                      ·
                        rfl

theorem cell23_2173087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_2173087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2173087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2173087 prefixEnd_2173087 := by exact prefixLift 2173087
  have htrace : WordTrace (prefixWord ++ tailWord_2173087) baseStart_2173087 baseEnd_2173087 := by
    simpa [prefixWord, tailWord_2173087, baseEnd_2173087] using wordTrace_append hprefix tailTrace_2173087
  have hstable : (prefixWord ++ tailWord_2173087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173087).length < 2 ^ (prefixWord ++ tailWord_2173087).sum := by decide
  have hdescent : baseEnd_2173087 < baseStart_2173087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173098 : List Nat := [3, 1, 5, 1, 2, 2, 1, 3, 1, 1, 3]
def baseStart_2173098 : Nat := 118140960795 + 2173098 * 2 ^ 59
def prefixEnd_2173098 : Nat := 4983230072969 + 3 ^ 40 * 2173098 * 2
def baseEnd_2173098 : Nat := 1115843783324243977781111

theorem tailTrace_2173098 : CollatzResearch.WordTrace tailWord_2173098 prefixEnd_2173098 1115843783324243977781111 := by
  unfold tailWord_2173098
  simp only [CollatzResearch.WordTrace]
  refine ⟨19814848870311139108973987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52839596987496370957263965 19814848870311139108973987)
  ·
    refine ⟨29722273305466708663460981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19814848870311139108973987 29722273305466708663460981)
    ·
      refine ⟨2786463122387503937199467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29722273305466708663460981 2786463122387503937199467)
      ·
        refine ⟨4179694683581255905799201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2786463122387503937199467 4179694683581255905799201)
        ·
          refine ⟨3134771012685941929349401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4179694683581255905799201 3134771012685941929349401)
          ·
            refine ⟨2351078259514456447012051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3134771012685941929349401 2351078259514456447012051)
            ·
              refine ⟨3526617389271684670518077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2351078259514456447012051 3526617389271684670518077)
              ·
                refine ⟨1322481520976881751444279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3526617389271684670518077 1322481520976881751444279)
                ·
                  refine ⟨1983722281465322627166419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1322481520976881751444279 1983722281465322627166419)
                  ·
                    refine ⟨2975583422197983940749629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1983722281465322627166419 2975583422197983940749629)
                    ·
                      refine ⟨1115843783324243977781111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2975583422197983940749629 1115843783324243977781111)
                      ·
                        rfl

theorem cell23_2173098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_2173098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2173098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2173098 prefixEnd_2173098 := by exact prefixLift 2173098
  have htrace : WordTrace (prefixWord ++ tailWord_2173098) baseStart_2173098 baseEnd_2173098 := by
    simpa [prefixWord, tailWord_2173098, baseEnd_2173098] using wordTrace_append hprefix tailTrace_2173098
  have hstable : (prefixWord ++ tailWord_2173098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173098).length < 2 ^ (prefixWord ++ tailWord_2173098).sum := by decide
  have hdescent : baseEnd_2173098 < baseStart_2173098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173103 : List Nat := [1, 1, 2, 1, 2, 3, 1, 3, 3, 3, 3]
def baseStart_2173103 : Nat := 118140960795 + 2173103 * 2 ^ 59
def prefixEnd_2173103 : Nat := 4983230072969 + 3 ^ 40 * 2173103 * 2
def baseEnd_2173103 : Nat := 1115846350727516458218587

theorem tailTrace_2173103 : CollatzResearch.WordTrace tailWord_2173103 prefixEnd_2173103 1115846350727516458218587 := by
  unfold tailWord_2173103
  simp only [CollatzResearch.WordTrace]
  refine ⟨79259577846226442289827963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52839718564150961526551975 79259577846226442289827963)
  ·
    refine ⟨118889366769339663434741945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79259577846226442289827963 118889366769339663434741945)
    ·
      refine ⟨89167025077004747576056459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118889366769339663434741945 89167025077004747576056459)
      ·
        refine ⟨133750537615507121364084689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89167025077004747576056459 133750537615507121364084689)
        ·
          refine ⟨100312903211630341023063517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133750537615507121364084689 100312903211630341023063517)
          ·
            refine ⟨37617338704361377883648819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100312903211630341023063517 37617338704361377883648819)
            ·
              refine ⟨56426008056542066825473229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37617338704361377883648819 56426008056542066825473229)
              ·
                refine ⟨21159753021203275059552461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56426008056542066825473229 21159753021203275059552461)
                ·
                  refine ⟨7934907382951228147332173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21159753021203275059552461 7934907382951228147332173)
                  ·
                    refine ⟨2975590268606710555249565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7934907382951228147332173 2975590268606710555249565)
                    ·
                      refine ⟨1115846350727516458218587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2975590268606710555249565 1115846350727516458218587)
                      ·
                        rfl

theorem cell23_2173103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3, 3, 3].length) (baseStart_2173103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2173103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2173103 prefixEnd_2173103 := by exact prefixLift 2173103
  have htrace : WordTrace (prefixWord ++ tailWord_2173103) baseStart_2173103 baseEnd_2173103 := by
    simpa [prefixWord, tailWord_2173103, baseEnd_2173103] using wordTrace_append hprefix tailTrace_2173103
  have hstable : (prefixWord ++ tailWord_2173103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173103).length < 2 ^ (prefixWord ++ tailWord_2173103).sum := by decide
  have hdescent : baseEnd_2173103 < baseStart_2173103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173108 : List Nat := [2, 5, 3, 1, 1, 1, 1, 2, 2, 3, 2]
def baseStart_2173108 : Nat := 118140960795 + 2173108 * 2 ^ 59
def prefixEnd_2173108 : Nat := 4983230072969 + 3 ^ 40 * 2173108 * 2
def baseEnd_2173108 : Nat := 1115848918130788938656065

theorem tailTrace_2173108 : CollatzResearch.WordTrace tailWord_2173108 prefixEnd_2173108 1115848918130788938656065 := by
  unfold tailWord_2173108
  simp only [CollatzResearch.WordTrace]
  refine ⟨39629880105604164071879989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52839840140805552095839985 39629880105604164071879989)
  ·
    refine ⟨3715301259900390381738749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39629880105604164071879989 3715301259900390381738749)
    ·
      refine ⟨1393237972462646393152031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3715301259900390381738749 1393237972462646393152031)
      ·
        refine ⟨2089856958693969589728047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1393237972462646393152031 2089856958693969589728047)
        ·
          refine ⟨3134785438040954384592071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2089856958693969589728047 3134785438040954384592071)
          ·
            refine ⟨4702178157061431576888107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3134785438040954384592071 4702178157061431576888107)
            ·
              refine ⟨7053267235592147365332161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4702178157061431576888107 7053267235592147365332161)
              ·
                refine ⟨5289950426694110523999121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7053267235592147365332161 5289950426694110523999121)
                ·
                  refine ⟨3967462820020582892999341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5289950426694110523999121 3967462820020582892999341)
                  ·
                    refine ⟨1487798557507718584874753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3967462820020582892999341 1487798557507718584874753)
                    ·
                      refine ⟨1115848918130788938656065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1487798557507718584874753 1115848918130788938656065)
                      ·
                        rfl

theorem cell23_2173108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_2173108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2173108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2173108 prefixEnd_2173108 := by exact prefixLift 2173108
  have htrace : WordTrace (prefixWord ++ tailWord_2173108) baseStart_2173108 baseEnd_2173108 := by
    simpa [prefixWord, tailWord_2173108, baseEnd_2173108] using wordTrace_append hprefix tailTrace_2173108
  have hstable : (prefixWord ++ tailWord_2173108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173108).length < 2 ^ (prefixWord ++ tailWord_2173108).sum := by decide
  have hdescent : baseEnd_2173108 < baseStart_2173108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173141 : List Nat := [1, 3, 2, 4, 3, 1, 1, 2, 1, 2, 3]
def baseStart_2173141 : Nat := 118140960795 + 2173141 * 2 ^ 59
def prefixEnd_2173141 : Nat := 4983230072969 + 3 ^ 40 * 2173141 * 2
def baseEnd_2173141 : Nat := 1115865862992387309543413

theorem tailTrace_2173141 : CollatzResearch.WordTrace tailWord_2173141 prefixEnd_2173141 1115865862992387309543413 := by
  unfold tailWord_2173141
  simp only [CollatzResearch.WordTrace]
  refine ⟨79260963820088774779711277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52840642546725849853140851 79260963820088774779711277)
  ·
    refine ⟨29722861432533290542391729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79260963820088774779711277 29722861432533290542391729)
    ·
      refine ⟨22292146074399967906793797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29722861432533290542391729 22292146074399967906793797)
      ·
        refine ⟨4179777388949993982523837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22292146074399967906793797 4179777388949993982523837)
        ·
          refine ⟨1567416520856247743446439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4179777388949993982523837 1567416520856247743446439)
          ·
            refine ⟨2351124781284371615169659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1567416520856247743446439 2351124781284371615169659)
            ·
              refine ⟨3526687171926557422754489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2351124781284371615169659 3526687171926557422754489)
              ·
                refine ⟨2645015378944918067065867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3526687171926557422754489 2645015378944918067065867)
                ·
                  refine ⟨3967523068417377100598801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2645015378944918067065867 3967523068417377100598801)
                  ·
                    refine ⟨2975642301313032825449101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3967523068417377100598801 2975642301313032825449101)
                    ·
                      refine ⟨1115865862992387309543413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2975642301313032825449101 1115865862992387309543413)
                      ·
                        rfl

theorem cell23_2173141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_2173141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2173141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2173141 prefixEnd_2173141 := by exact prefixLift 2173141
  have htrace : WordTrace (prefixWord ++ tailWord_2173141) baseStart_2173141 baseEnd_2173141 := by
    simpa [prefixWord, tailWord_2173141, baseEnd_2173141] using wordTrace_append hprefix tailTrace_2173141
  have hstable : (prefixWord ++ tailWord_2173141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173141).length < 2 ^ (prefixWord ++ tailWord_2173141).sum := by decide
  have hdescent : baseEnd_2173141 < baseStart_2173141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173163 : List Nat := [1, 1, 1, 1, 2, 5, 1, 3, 2, 1, 5]
def baseStart_2173163 : Nat := 118140960795 + 2173163 * 2 ^ 59
def prefixEnd_2173163 : Nat := 4983230072969 + 3 ^ 40 * 2173163 * 2
def baseEnd_2173163 : Nat := 1115877159566786223468311

theorem tailTrace_2173163 : CollatzResearch.WordTrace tailWord_2173163 prefixEnd_2173163 1115877159566786223468311 := by
  unfold tailWord_2173163
  simp only [CollatzResearch.WordTrace]
  refine ⟨79261766226009072537012143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52841177484006048358008095 79261766226009072537012143)
  ·
    refine ⟨118892649339013608805518215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79261766226009072537012143 118892649339013608805518215)
    ·
      refine ⟨178338974008520413208277323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118892649339013608805518215 178338974008520413208277323)
      ·
        refine ⟨267508461012780619812415985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178338974008520413208277323 267508461012780619812415985)
        ·
          refine ⟨200631345759585464859311989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 267508461012780619812415985 200631345759585464859311989)
          ·
            refine ⟨18809188664961137330560499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 200631345759585464859311989 18809188664961137330560499)
            ·
              refine ⟨28213782997441705995840749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18809188664961137330560499 28213782997441705995840749)
              ·
                refine ⟨10580168624040639748440281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28213782997441705995840749 10580168624040639748440281)
                ·
                  refine ⟨7935126468030479811330211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10580168624040639748440281 7935126468030479811330211)
                  ·
                    refine ⟨11902689702045719716995317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7935126468030479811330211 11902689702045719716995317)
                    ·
                      refine ⟨1115877159566786223468311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11902689702045719716995317 1115877159566786223468311)
                      ·
                        rfl

theorem cell23_2173163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2, 1, 5].length) (baseStart_2173163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2173163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2173163 prefixEnd_2173163 := by exact prefixLift 2173163
  have htrace : WordTrace (prefixWord ++ tailWord_2173163) baseStart_2173163 baseEnd_2173163 := by
    simpa [prefixWord, tailWord_2173163, baseEnd_2173163] using wordTrace_append hprefix tailTrace_2173163
  have hstable : (prefixWord ++ tailWord_2173163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173163).length < 2 ^ (prefixWord ++ tailWord_2173163).sum := by decide
  have hdescent : baseEnd_2173163 < baseStart_2173163 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173164 : List Nat := [2, 2, 1, 1, 2, 3, 5, 1, 1, 3, 2]
def baseStart_2173164 : Nat := 118140960795 + 2173164 * 2 ^ 59
def prefixEnd_2173164 : Nat := 4983230072969 + 3 ^ 40 * 2173164 * 2
def baseEnd_2173164 : Nat := 1115877673047440719555807

theorem tailTrace_2173164 : CollatzResearch.WordTrace tailWord_2173164 prefixEnd_2173164 1115877673047440719555807 := by
  unfold tailWord_2173164
  simp only [CollatzResearch.WordTrace]
  refine ⟨39630901349502724853899273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52841201799336966471865697 39630901349502724853899273)
  ·
    refine ⟨29723176012127043640424455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39630901349502724853899273 29723176012127043640424455)
    ·
      refine ⟨44584764018190565460636683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29723176012127043640424455 44584764018190565460636683)
      ·
        refine ⟨66877146027285848190955025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44584764018190565460636683 66877146027285848190955025)
        ·
          refine ⟨50157859520464386143216269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66877146027285848190955025 50157859520464386143216269)
          ·
            refine ⟨18809197320174144803706101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50157859520464386143216269 18809197320174144803706101)
            ·
              refine ⟨1763362248766326075347447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18809197320174144803706101 1763362248766326075347447)
              ·
                refine ⟨2645043373149489113021171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1763362248766326075347447 2645043373149489113021171)
                ·
                  refine ⟨3967565059724233669531757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2645043373149489113021171 3967565059724233669531757)
                  ·
                    refine ⟨1487836897396587626074409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3967565059724233669531757 1487836897396587626074409)
                    ·
                      refine ⟨1115877673047440719555807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1487836897396587626074409 1115877673047440719555807)
                      ·
                        rfl

theorem cell23_2173164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 3, 2].length) (baseStart_2173164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2173164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2173164 prefixEnd_2173164 := by exact prefixLift 2173164
  have htrace : WordTrace (prefixWord ++ tailWord_2173164) baseStart_2173164 baseEnd_2173164 := by
    simpa [prefixWord, tailWord_2173164, baseEnd_2173164] using wordTrace_append hprefix tailTrace_2173164
  have hstable : (prefixWord ++ tailWord_2173164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173164).length < 2 ^ (prefixWord ++ tailWord_2173164).sum := by decide
  have hdescent : baseEnd_2173164 < baseStart_2173164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173180 : List Nat := [2, 2, 2, 1, 4, 1, 1, 1, 2, 4, 3]
def baseStart_2173180 : Nat := 118140960795 + 2173180 * 2 ^ 59
def prefixEnd_2173180 : Nat := 4983230072969 + 3 ^ 40 * 2173180 * 2
def baseEnd_2173180 : Nat := 1115885888737912656955733

theorem tailTrace_2173180 : CollatzResearch.WordTrace tailWord_2173180 prefixEnd_2173180 1115885888737912656955733 := by
  unfold tailWord_2173180
  simp only [CollatzResearch.WordTrace]
  refine ⟨39631193133473742220190497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52841590844631656293587329 39631193133473742220190497)
  ·
    refine ⟨29723394850105306665142873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39631193133473742220190497 29723394850105306665142873)
    ·
      refine ⟨22292546137578979998857155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29723394850105306665142873 22292546137578979998857155)
      ·
        refine ⟨33438819206368469998285733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22292546137578979998857155 33438819206368469998285733)
        ·
          refine ⟨6269778601194088124678575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33438819206368469998285733 6269778601194088124678575)
          ·
            refine ⟨9404667901791132187017863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6269778601194088124678575 9404667901791132187017863)
            ·
              refine ⟨14107001852686698280526795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9404667901791132187017863 14107001852686698280526795)
              ·
                refine ⟨21160502779030047420790193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14107001852686698280526795 21160502779030047420790193)
                ·
                  refine ⟨15870377084272535565592645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21160502779030047420790193 15870377084272535565592645)
                  ·
                    refine ⟨2975695703301100418548621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15870377084272535565592645 2975695703301100418548621)
                    ·
                      refine ⟨1115885888737912656955733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2975695703301100418548621 1115885888737912656955733)
                      ·
                        rfl

theorem cell23_2173180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 2, 4, 3].length) (baseStart_2173180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2173180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2173180 prefixEnd_2173180 := by exact prefixLift 2173180
  have htrace : WordTrace (prefixWord ++ tailWord_2173180) baseStart_2173180 baseEnd_2173180 := by
    simpa [prefixWord, tailWord_2173180, baseEnd_2173180] using wordTrace_append hprefix tailTrace_2173180
  have hstable : (prefixWord ++ tailWord_2173180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173180).length < 2 ^ (prefixWord ++ tailWord_2173180).sum := by decide
  have hdescent : baseEnd_2173180 < baseStart_2173180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173183 : List Nat := [1, 1, 2, 2, 1, 4, 2, 3, 7]
def baseStart_2173183 : Nat := 118140960795 + 2173183 * 2 ^ 59
def prefixEnd_2173183 : Nat := 4983230072969 + 3 ^ 40 * 2173183 * 2
def baseEnd_2173183 : Nat := 123987492131097349468691

theorem tailTrace_2173183 : CollatzResearch.WordTrace tailWord_2173183 prefixEnd_2173183 123987492131097349468691 := by
  unfold tailWord_2173183
  simp only [CollatzResearch.WordTrace]
  refine ⟨79262495685936615952740203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52841663790624410635160135 79262495685936615952740203)
  ·
    refine ⟨118893743528904923929110305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79262495685936615952740203 118893743528904923929110305)
    ·
      refine ⟨89170307646678692946832729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118893743528904923929110305 89170307646678692946832729)
      ·
        refine ⟨66877730735009019710124547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89170307646678692946832729 66877730735009019710124547)
        ·
          refine ⟨100316596102513529565186821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66877730735009019710124547 100316596102513529565186821)
          ·
            refine ⟨18809361769221286793472529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100316596102513529565186821 18809361769221286793472529)
            ·
              refine ⟨14107021326915965095104397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18809361769221286793472529 14107021326915965095104397)
              ·
                refine ⟨5290132997593486910664149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14107021326915965095104397 5290132997593486910664149)
                ·
                  refine ⟨123987492131097349468691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5290132997593486910664149 123987492131097349468691)
                  ·
                    rfl

theorem cell23_2173183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3, 7].length) (baseStart_2173183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2173183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2173183 prefixEnd_2173183 := by exact prefixLift 2173183
  have htrace : WordTrace (prefixWord ++ tailWord_2173183) baseStart_2173183 baseEnd_2173183 := by
    simpa [prefixWord, tailWord_2173183, baseEnd_2173183] using wordTrace_append hprefix tailTrace_2173183
  have hstable : (prefixWord ++ tailWord_2173183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173183).length < 2 ^ (prefixWord ++ tailWord_2173183).sum := by decide
  have hdescent : baseEnd_2173183 < baseStart_2173183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173194 : List Nat := [3, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2]
def baseStart_2173194 : Nat := 118140960795 + 2173194 * 2 ^ 59
def prefixEnd_2173194 : Nat := 4983230072969 + 3 ^ 40 * 2173194 * 2
def baseEnd_2173194 : Nat := 1115893077467075602180669

theorem tailTrace_2173194 : CollatzResearch.WordTrace tailWord_2173194 prefixEnd_2173194 1115893077467075602180669 := by
  unfold tailWord_2173194
  simp only [CollatzResearch.WordTrace]
  refine ⟨19815724222224191207847659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52841931259264509887593757 19815724222224191207847659)
  ·
    refine ⟨29723586333336286811771489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19815724222224191207847659 29723586333336286811771489)
    ·
      refine ⟨22292689750002215108828617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29723586333336286811771489 22292689750002215108828617)
      ·
        refine ⟨16719517312501661331621463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22292689750002215108828617 16719517312501661331621463)
        ·
          refine ⟨25079275968752491997432195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16719517312501661331621463 25079275968752491997432195)
          ·
            refine ⟨37618913953128737996148293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25079275968752491997432195 37618913953128737996148293)
            ·
              refine ⟨7053546366211638374277805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37618913953128737996148293 7053546366211638374277805)
              ·
                refine ⟨2645079887329364390354177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7053546366211638374277805 2645079887329364390354177)
                ·
                  refine ⟨1983809915497023292765633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2645079887329364390354177 1983809915497023292765633)
                  ·
                    refine ⟨1487857436622767469574225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1983809915497023292765633 1487857436622767469574225)
                    ·
                      refine ⟨1115893077467075602180669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1487857436622767469574225 1115893077467075602180669)
                      ·
                        rfl

theorem cell23_2173194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2].length) (baseStart_2173194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2173194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2173194 prefixEnd_2173194 := by exact prefixLift 2173194
  have htrace : WordTrace (prefixWord ++ tailWord_2173194) baseStart_2173194 baseEnd_2173194 := by
    simpa [prefixWord, tailWord_2173194, baseEnd_2173194] using wordTrace_append hprefix tailTrace_2173194
  have hstable : (prefixWord ++ tailWord_2173194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173194).length < 2 ^ (prefixWord ++ tailWord_2173194).sum := by decide
  have hdescent : baseEnd_2173194 < baseStart_2173194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173263 : List Nat := [1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 6]
def baseStart_2173263 : Nat := 118140960795 + 2173263 * 2 ^ 59
def prefixEnd_2173263 : Nat := 4983230072969 + 3 ^ 40 * 2173263 * 2
def baseEnd_2173263 : Nat := 1115928507632235832217851

theorem tailTrace_2173263 : CollatzResearch.WordTrace tailWord_2173263 prefixEnd_2173263 1115928507632235832217851 := by
  unfold tailWord_2173263
  simp only [CollatzResearch.WordTrace]
  refine ⟨79265413525646789615652443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52843609017097859743768295 79265413525646789615652443)
  ·
    refine ⟨118898120288470184423478665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79265413525646789615652443 118898120288470184423478665)
    ·
      refine ⟨89173590216352638317608999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118898120288470184423478665 89173590216352638317608999)
      ·
        refine ⟨133760385324528957476413499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89173590216352638317608999 133760385324528957476413499)
        ·
          refine ⟨200640577986793436214620249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133760385324528957476413499 200640577986793436214620249)
          ·
            refine ⟨150480433490095077160965187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200640577986793436214620249 150480433490095077160965187)
            ·
              refine ⟨225720650235142615741447781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150480433490095077160965187 225720650235142615741447781)
              ·
                refine ⟨42322621919089240451521459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 225720650235142615741447781 42322621919089240451521459)
                ·
                  refine ⟨63483932878633860677282189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42322621919089240451521459 63483932878633860677282189)
                  ·
                    refine ⟨23806474829487697753980821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 63483932878633860677282189 23806474829487697753980821)
                    ·
                      refine ⟨1115928507632235832217851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23806474829487697753980821 1115928507632235832217851)
                      ·
                        rfl

theorem cell23_2173263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 6].length) (baseStart_2173263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2173263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2173263 prefixEnd_2173263 := by exact prefixLift 2173263
  have htrace : WordTrace (prefixWord ++ tailWord_2173263) baseStart_2173263 baseEnd_2173263 := by
    simpa [prefixWord, tailWord_2173263, baseEnd_2173263] using wordTrace_append hprefix tailTrace_2173263
  have hstable : (prefixWord ++ tailWord_2173263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173263).length < 2 ^ (prefixWord ++ tailWord_2173263).sum := by decide
  have hdescent : baseEnd_2173263 < baseStart_2173263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173287 : List Nat := [1, 1, 5, 1, 3, 1, 1, 1, 4, 2, 3]
def baseStart_2173287 : Nat := 118140960795 + 2173287 * 2 ^ 59
def prefixEnd_2173287 : Nat := 4983230072969 + 3 ^ 40 * 2173287 * 2
def baseEnd_2173287 : Nat := 1115940831167943738317741

theorem tailTrace_2173287 : CollatzResearch.WordTrace tailWord_2173287 prefixEnd_2173287 1115940831167943738317741 := by
  unfold tailWord_2173287
  simp only [CollatzResearch.WordTrace]
  refine ⟨79266288877559841714526115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52844192585039894476350743 79266288877559841714526115)
  ·
    refine ⟨118899433316339762571789173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79266288877559841714526115 118899433316339762571789173)
    ·
      refine ⟨11146821873406852741105235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 118899433316339762571789173 11146821873406852741105235)
      ·
        refine ⟨16720232810110279111657853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11146821873406852741105235 16720232810110279111657853)
        ·
          refine ⟨6270087303791354666871695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16720232810110279111657853 6270087303791354666871695)
          ·
            refine ⟨9405130955687032000307543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6270087303791354666871695 9405130955687032000307543)
            ·
              refine ⟨14107696433530548000461315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9405130955687032000307543 14107696433530548000461315)
              ·
                refine ⟨21161544650295822000691973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14107696433530548000461315 21161544650295822000691973)
                ·
                  refine ⟨3967789621930466625129745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21161544650295822000691973 3967789621930466625129745)
                  ·
                    refine ⟨2975842216447849968847309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3967789621930466625129745 2975842216447849968847309)
                    ·
                      refine ⟨1115940831167943738317741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2975842216447849968847309 1115940831167943738317741)
                      ·
                        rfl

theorem cell23_2173287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_2173287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2173287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2173287 prefixEnd_2173287 := by exact prefixLift 2173287
  have htrace : WordTrace (prefixWord ++ tailWord_2173287) baseStart_2173287 baseEnd_2173287 := by
    simpa [prefixWord, tailWord_2173287, baseEnd_2173287] using wordTrace_append hprefix tailTrace_2173287
  have hstable : (prefixWord ++ tailWord_2173287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173287).length < 2 ^ (prefixWord ++ tailWord_2173287).sum := by decide
  have hdescent : baseEnd_2173287 < baseStart_2173287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173307 : List Nat := [1, 1, 1, 1, 1, 7, 4, 1, 6]
def baseStart_2173307 : Nat := 118140960795 + 2173307 * 2 ^ 59
def prefixEnd_2173307 : Nat := 4983230072969 + 3 ^ 40 * 2173307 * 2
def baseEnd_2173307 : Nat := 123994566753448184451961

theorem tailTrace_2173307 : CollatzResearch.WordTrace tailWord_2173307 prefixEnd_2173307 123994566753448184451961 := by
  unfold tailWord_2173307
  simp only [CollatzResearch.WordTrace]
  refine ⟨79267018337487385130254175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52844678891658256753502783 79267018337487385130254175)
  ·
    refine ⟨118900527506231077695381263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79267018337487385130254175 118900527506231077695381263)
    ·
      refine ⟨178350791259346616543071895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118900527506231077695381263 178350791259346616543071895)
      ·
        refine ⟨267526186889019924814607843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178350791259346616543071895 267526186889019924814607843)
        ·
          refine ⟨401289280333529887221911765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267526186889019924814607843 401289280333529887221911765)
          ·
            refine ⟨9405217507817106731763557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 401289280333529887221911765 9405217507817106731763557)
            ·
              refine ⟨1763478282715707512205667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9405217507817106731763557 1763478282715707512205667)
              ·
                refine ⟨2645217424073561268308501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1763478282715707512205667 2645217424073561268308501)
                ·
                  refine ⟨123994566753448184451961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2645217424073561268308501 123994566753448184451961)
                  ·
                    rfl

theorem cell23_2173307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 1, 6].length) (baseStart_2173307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2173307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2173307 prefixEnd_2173307 := by exact prefixLift 2173307
  have htrace : WordTrace (prefixWord ++ tailWord_2173307) baseStart_2173307 baseEnd_2173307 := by
    simpa [prefixWord, tailWord_2173307, baseEnd_2173307] using wordTrace_append hprefix tailTrace_2173307
  have hstable : (prefixWord ++ tailWord_2173307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173307).length < 2 ^ (prefixWord ++ tailWord_2173307).sum := by decide
  have hdescent : baseEnd_2173307 < baseStart_2173307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173317 : List Nat := [1, 3, 1, 1, 3, 1, 1, 3, 5, 1, 3]
def baseStart_2173317 : Nat := 118140960795 + 2173317 * 2 ^ 59
def prefixEnd_2173317 : Nat := 4983230072969 + 3 ^ 40 * 2173317 * 2
def baseEnd_2173317 : Nat := 1115956235587578620942603

theorem tailTrace_2173317 : CollatzResearch.WordTrace tailWord_2173317 prefixEnd_2173317 1115956235587578620942603 := by
  unfold tailWord_2173317
  simp only [CollatzResearch.WordTrace]
  refine ⟨79267383067451156838118205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52844922044967437892078803 79267383067451156838118205)
  ·
    refine ⟨29725268650294183814294327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79267383067451156838118205 29725268650294183814294327)
    ·
      refine ⟨44587902975441275721441491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29725268650294183814294327 44587902975441275721441491)
      ·
        refine ⟨66881854463161913582162237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44587902975441275721441491 66881854463161913582162237)
        ·
          refine ⟨25080695423685717593310839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66881854463161913582162237 25080695423685717593310839)
          ·
            refine ⟨37621043135528576389966259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25080695423685717593310839 37621043135528576389966259)
            ·
              refine ⟨56431564703292864584949389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37621043135528576389966259 56431564703292864584949389)
              ·
                refine ⟨21161836763734824219356021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56431564703292864584949389 21161836763734824219356021)
                ·
                  refine ⟨1983922196600139770564627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21161836763734824219356021 1983922196600139770564627)
                  ·
                    refine ⟨2975883294900209655846941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1983922196600139770564627 2975883294900209655846941)
                    ·
                      refine ⟨1115956235587578620942603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2975883294900209655846941 1115956235587578620942603)
                      ·
                        rfl

theorem cell23_2173317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 5, 1, 3].length) (baseStart_2173317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2173317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2173317 prefixEnd_2173317 := by exact prefixLift 2173317
  have htrace : WordTrace (prefixWord ++ tailWord_2173317) baseStart_2173317 baseEnd_2173317 := by
    simpa [prefixWord, tailWord_2173317, baseEnd_2173317] using wordTrace_append hprefix tailTrace_2173317
  have hstable : (prefixWord ++ tailWord_2173317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173317).length < 2 ^ (prefixWord ++ tailWord_2173317).sum := by decide
  have hdescent : baseEnd_2173317 < baseStart_2173317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173344 : List Nat := [2, 1, 1, 4, 1, 3, 2, 2, 2, 3, 2]
def baseStart_2173344 : Nat := 118140960795 + 2173344 * 2 ^ 59
def prefixEnd_2173344 : Nat := 4983230072969 + 3 ^ 40 * 2173344 * 2
def baseEnd_2173344 : Nat := 1115970099565250015304979

theorem tailTrace_2173344 : CollatzResearch.WordTrace tailWord_2173344 prefixEnd_2173344 1115970099565250015304979 := by
  unfold tailWord_2173344
  simp only [CollatzResearch.WordTrace]
  refine ⟨39634183919176670224675543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52845578558902226966234057 39634183919176670224675543)
  ·
    refine ⟨59451275878765005337013315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39634183919176670224675543 59451275878765005337013315)
    ·
      refine ⟨89176913818147508005519973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59451275878765005337013315 89176913818147508005519973)
      ·
        refine ⟨16720671340902657751034995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89176913818147508005519973 16720671340902657751034995)
        ·
          refine ⟨25081007011353986626552493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16720671340902657751034995 25081007011353986626552493)
          ·
            refine ⟨9405377629257744984957185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25081007011353986626552493 9405377629257744984957185)
            ·
              refine ⟨7054033221943308738717889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9405377629257744984957185 7054033221943308738717889)
              ·
                refine ⟨5290524916457481554038417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7054033221943308738717889 5290524916457481554038417)
                ·
                  refine ⟨3967893687343111165528813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5290524916457481554038417 3967893687343111165528813)
                  ·
                    refine ⟨1487960132753666687073305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3967893687343111165528813 1487960132753666687073305)
                    ·
                      refine ⟨1115970099565250015304979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1487960132753666687073305 1115970099565250015304979)
                      ·
                        rfl

theorem cell23_2173344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2, 2, 3, 2].length) (baseStart_2173344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2173344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2173344 prefixEnd_2173344 := by exact prefixLift 2173344
  have htrace : WordTrace (prefixWord ++ tailWord_2173344) baseStart_2173344 baseEnd_2173344 := by
    simpa [prefixWord, tailWord_2173344, baseEnd_2173344] using wordTrace_append hprefix tailTrace_2173344
  have hstable : (prefixWord ++ tailWord_2173344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173344).length < 2 ^ (prefixWord ++ tailWord_2173344).sum := by decide
  have hdescent : baseEnd_2173344 < baseStart_2173344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173345 : List Nat := [1, 2, 3, 5, 1, 2, 2, 2, 1, 4]
def baseStart_2173345 : Nat := 118140960795 + 2173345 * 2 ^ 59
def prefixEnd_2173345 : Nat := 4983230072969 + 3 ^ 40 * 2173345 * 2
def baseEnd_2173345 : Nat := 371990204348634837130825

theorem tailTrace_2173345 : CollatzResearch.WordTrace tailWord_2173345 prefixEnd_2173345 371990204348634837130825 := by
  unfold tailWord_2173345
  simp only [CollatzResearch.WordTrace]
  refine ⟨79268404311349717620137489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52845602874233145080091659 79268404311349717620137489)
  ·
    refine ⟨59451303233512288215103117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79268404311349717620137489 59451303233512288215103117)
    ·
      refine ⟨22294238712567108080663669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59451303233512288215103117 22294238712567108080663669)
      ·
        refine ⟨2090084879303166382562219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22294238712567108080663669 2090084879303166382562219)
        ·
          refine ⟨3135127318954749573843329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2090084879303166382562219 3135127318954749573843329)
          ·
            refine ⟨2351345489216062180382497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3135127318954749573843329 2351345489216062180382497)
            ·
              refine ⟨1763509116912046635286873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2351345489216062180382497 1763509116912046635286873)
              ·
                refine ⟨1322631837684034976465155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1763509116912046635286873 1322631837684034976465155)
                ·
                  refine ⟨1983947756526052464697733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1322631837684034976465155 1983947756526052464697733)
                  ·
                    refine ⟨371990204348634837130825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1983947756526052464697733 371990204348634837130825)
                    ·
                      rfl

theorem cell23_2173345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 2, 1, 4].length) (baseStart_2173345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2173345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2173345 prefixEnd_2173345 := by exact prefixLift 2173345
  have htrace : WordTrace (prefixWord ++ tailWord_2173345) baseStart_2173345 baseEnd_2173345 := by
    simpa [prefixWord, tailWord_2173345, baseEnd_2173345] using wordTrace_append hprefix tailTrace_2173345
  have hstable : (prefixWord ++ tailWord_2173345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173345).length < 2 ^ (prefixWord ++ tailWord_2173345).sum := by decide
  have hdescent : baseEnd_2173345 < baseStart_2173345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173367 : List Nat := [1, 1, 3, 1, 3, 4, 2, 1, 1, 6]
def baseStart_2173367 : Nat := 118140960795 + 2173367 * 2 ^ 59
def prefixEnd_2173367 : Nat := 4983230072969 + 3 ^ 40 * 2173367 * 2
def baseEnd_2173367 : Nat := 371993969873434475105791

theorem tailTrace_2173367 : CollatzResearch.WordTrace tailWord_2173367 prefixEnd_2173367 371993969873434475105791 := by
  unfold tailWord_2173367
  simp only [CollatzResearch.WordTrace]
  refine ⟨79269206717270015377438355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52846137811513343584958903 79269206717270015377438355)
  ·
    refine ⟨118903810075905023066157533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79269206717270015377438355 118903810075905023066157533)
    ·
      refine ⟨44588928778464383649809075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118903810075905023066157533 44588928778464383649809075)
      ·
        refine ⟨66883393167696575474713613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44588928778464383649809075 66883393167696575474713613)
        ·
          refine ⟨25081272437886215803017605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66883393167696575474713613 25081272437886215803017605)
          ·
            refine ⟨4702738582103665463065801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25081272437886215803017605 4702738582103665463065801)
            ·
              refine ⟨3527053936577749097299351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4702738582103665463065801 3527053936577749097299351)
              ·
                refine ⟨5290580904866623645949027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3527053936577749097299351 5290580904866623645949027)
                ·
                  refine ⟨7935871357299935468923541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5290580904866623645949027 7935871357299935468923541)
                  ·
                    refine ⟨371993969873434475105791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7935871357299935468923541 371993969873434475105791)
                    ·
                      rfl

theorem cell23_2173367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 1, 6].length) (baseStart_2173367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2173367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2173367 prefixEnd_2173367 := by exact prefixLift 2173367
  have htrace : WordTrace (prefixWord ++ tailWord_2173367) baseStart_2173367 baseEnd_2173367 := by
    simpa [prefixWord, tailWord_2173367, baseEnd_2173367] using wordTrace_append hprefix tailTrace_2173367
  have hstable : (prefixWord ++ tailWord_2173367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173367).length < 2 ^ (prefixWord ++ tailWord_2173367).sum := by decide
  have hdescent : baseEnd_2173367 < baseStart_2173367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173370 : List Nat := [3, 1, 1, 1, 2, 1, 1, 5, 1, 1, 6]
def baseStart_2173370 : Nat := 118140960795 + 2173370 * 2 ^ 59
def prefixEnd_2173370 : Nat := 4983230072969 + 3 ^ 40 * 2173370 * 2
def baseEnd_2173370 : Nat := 1115983450062266913579859

theorem tailTrace_2173370 : CollatzResearch.WordTrace tailWord_2173370 prefixEnd_2173370 1115983450062266913579859 := by
  unfold tailWord_2173370
  simp only [CollatzResearch.WordTrace]
  refine ⟨19817329034064786722449391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52846210757506097926531709 19817329034064786722449391)
  ·
    refine ⟨29725993551097180083674087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19817329034064786722449391 29725993551097180083674087)
    ·
      refine ⟨44588990326645770125511131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29725993551097180083674087 44588990326645770125511131)
      ·
        refine ⟨66883485489968655188266697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44588990326645770125511131 66883485489968655188266697)
        ·
          refine ⟨50162614117476491391200023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66883485489968655188266697 50162614117476491391200023)
          ·
            refine ⟨75243921176214737086800035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50162614117476491391200023 75243921176214737086800035)
            ·
              refine ⟨112865881764322105630200053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75243921176214737086800035 112865881764322105630200053)
              ·
                refine ⟨10581176415405197402831255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 112865881764322105630200053 10581176415405197402831255)
                ·
                  refine ⟨15871764623107796104246883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10581176415405197402831255 15871764623107796104246883)
                  ·
                    refine ⟨23807646934661694156370325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15871764623107796104246883 23807646934661694156370325)
                    ·
                      refine ⟨1115983450062266913579859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23807646934661694156370325 1115983450062266913579859)
                      ·
                        rfl

theorem cell23_2173370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 1, 1, 6].length) (baseStart_2173370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2173370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2173370 prefixEnd_2173370 := by exact prefixLift 2173370
  have htrace : WordTrace (prefixWord ++ tailWord_2173370) baseStart_2173370 baseEnd_2173370 := by
    simpa [prefixWord, tailWord_2173370, baseEnd_2173370] using wordTrace_append hprefix tailTrace_2173370
  have hstable : (prefixWord ++ tailWord_2173370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173370).length < 2 ^ (prefixWord ++ tailWord_2173370).sum := by decide
  have hdescent : baseEnd_2173370 < baseStart_2173370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173388 : List Nat := [2, 2, 1, 4, 4, 1, 2, 1, 1, 5]
def baseStart_2173388 : Nat := 118140960795 + 2173388 * 2 ^ 59
def prefixEnd_2173388 : Nat := 4983230072969 + 3 ^ 40 * 2173388 * 2
def baseEnd_2173388 : Nat := 371997564238015947718259

theorem tailTrace_2173388 : CollatzResearch.WordTrace tailWord_2173388 prefixEnd_2173388 371997564238015947718259 := by
  unfold tailWord_2173388
  simp only [CollatzResearch.WordTrace]
  refine ⟨39634986325096967981976409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52846648433462623975968545 39634986325096967981976409)
  ·
    refine ⟨29726239743822725986482307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39634986325096967981976409 29726239743822725986482307)
    ·
      refine ⟨44589359615734088979723461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29726239743822725986482307 44589359615734088979723461)
      ·
        refine ⟨8360504927950141683698149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44589359615734088979723461 8360504927950141683698149)
        ·
          refine ⟨1567594673990651565693403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8360504927950141683698149 1567594673990651565693403)
          ·
            refine ⟨2351392010985977348540105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1567594673990651565693403 2351392010985977348540105)
            ·
              refine ⟨1763544008239483011405079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2351392010985977348540105 1763544008239483011405079)
              ·
                refine ⟨2645316012359224517107619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1763544008239483011405079 2645316012359224517107619)
                ·
                  refine ⟨3967974018538836775661429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2645316012359224517107619 3967974018538836775661429)
                  ·
                    refine ⟨371997564238015947718259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3967974018538836775661429 371997564238015947718259)
                    ·
                      rfl

theorem cell23_2173388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 1, 1, 5].length) (baseStart_2173388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2173388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2173388 prefixEnd_2173388 := by exact prefixLift 2173388
  have htrace : WordTrace (prefixWord ++ tailWord_2173388) baseStart_2173388 baseEnd_2173388 := by
    simpa [prefixWord, tailWord_2173388, baseEnd_2173388] using wordTrace_append hprefix tailTrace_2173388
  have hstable : (prefixWord ++ tailWord_2173388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173388).length < 2 ^ (prefixWord ++ tailWord_2173388).sum := by decide
  have hdescent : baseEnd_2173388 < baseStart_2173388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173400 : List Nat := [2, 1, 2, 2, 2, 1, 1, 2, 2, 2, 6]
def baseStart_2173400 : Nat := 118140960795 + 2173400 * 2 ^ 59
def prefixEnd_2173400 : Nat := 4983230072969 + 3 ^ 40 * 2173400 * 2
def baseEnd_2173400 : Nat := 1115998854481901796204721

theorem tailTrace_2173400 : CollatzResearch.WordTrace tailWord_2173400 prefixEnd_2173400 1115998854481901796204721 := by
  unfold tailWord_2173400
  simp only [CollatzResearch.WordTrace]
  refine ⟨39635205163075231006694827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52846940217433641342259769 39635205163075231006694827)
  ·
    refine ⟨59452807744612846510042241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39635205163075231006694827 59452807744612846510042241)
    ·
      refine ⟨44589605808459634882531681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59452807744612846510042241 44589605808459634882531681)
      ·
        refine ⟨33442204356344726161898761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44589605808459634882531681 33442204356344726161898761)
        ·
          refine ⟨25081653267258544621424071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33442204356344726161898761 25081653267258544621424071)
          ·
            refine ⟨37622479900887816932136107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25081653267258544621424071 37622479900887816932136107)
            ·
              refine ⟨56433719851331725398204161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37622479900887816932136107 56433719851331725398204161)
              ·
                refine ⟨42325289888498794048653121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56433719851331725398204161 42325289888498794048653121)
                ·
                  refine ⟨31743967416374095536489841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42325289888498794048653121 31743967416374095536489841)
                  ·
                    refine ⟨23807975562280571652367381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31743967416374095536489841 23807975562280571652367381)
                    ·
                      refine ⟨1115998854481901796204721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23807975562280571652367381 1115998854481901796204721)
                      ·
                        rfl

theorem cell23_2173400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_2173400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2173400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2173400 prefixEnd_2173400 := by exact prefixLift 2173400
  have htrace : WordTrace (prefixWord ++ tailWord_2173400) baseStart_2173400 baseEnd_2173400 := by
    simpa [prefixWord, tailWord_2173400, baseEnd_2173400] using wordTrace_append hprefix tailTrace_2173400
  have hstable : (prefixWord ++ tailWord_2173400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173400).length < 2 ^ (prefixWord ++ tailWord_2173400).sum := by decide
  have hdescent : baseEnd_2173400 < baseStart_2173400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173417 : List Nat := [1, 2, 1, 1, 1, 2, 1, 3, 2, 7, 2]
def baseStart_2173417 : Nat := 118140960795 + 2173417 * 2 ^ 59
def prefixEnd_2173417 : Nat := 4983230072969 + 3 ^ 40 * 2173417 * 2
def baseEnd_2173417 : Nat := 1116007583653028229692143

theorem tailTrace_2173417 : CollatzResearch.WordTrace tailWord_2173417 prefixEnd_2173417 1116007583653028229692143 := by
  unfold tailWord_2173417
  simp only [CollatzResearch.WordTrace]
  refine ⟨79271030367088873916758505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52847353578059249277839003 79271030367088873916758505)
  ·
    refine ⟨59453272775316655437568879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79271030367088873916758505 59453272775316655437568879)
    ·
      refine ⟨89179909162974983156353319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59453272775316655437568879 89179909162974983156353319)
      ·
        refine ⟨133769863744462474734529979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89179909162974983156353319 133769863744462474734529979)
        ·
          refine ⟨200654795616693712101794969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133769863744462474734529979 200654795616693712101794969)
          ·
            refine ⟨150491096712520284076346227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200654795616693712101794969 150491096712520284076346227)
            ·
              refine ⟨225736645068780426114519341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150491096712520284076346227 225736645068780426114519341)
              ·
                refine ⟨84651241900792659792944753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 225736645068780426114519341 84651241900792659792944753)
                ·
                  refine ⟨63488431425594494844708565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84651241900792659792944753 63488431425594494844708565)
                  ·
                    refine ⟨1488010111537370972922857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 63488431425594494844708565 1488010111537370972922857)
                    ·
                      refine ⟨1116007583653028229692143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1488010111537370972922857 1116007583653028229692143)
                      ·
                        rfl

theorem cell23_2173417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 7, 2].length) (baseStart_2173417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2173417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2173417 prefixEnd_2173417 := by exact prefixLift 2173417
  have htrace : WordTrace (prefixWord ++ tailWord_2173417) baseStart_2173417 baseEnd_2173417 := by
    simpa [prefixWord, tailWord_2173417, baseEnd_2173417] using wordTrace_append hprefix tailTrace_2173417
  have hstable : (prefixWord ++ tailWord_2173417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173417).length < 2 ^ (prefixWord ++ tailWord_2173417).sum := by decide
  have hdescent : baseEnd_2173417 < baseStart_2173417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173421 : List Nat := [1, 5, 1, 3, 1, 3, 1, 1, 1, 2, 4]
def baseStart_2173421 : Nat := 118140960795 + 2173421 * 2 ^ 59
def prefixEnd_2173421 : Nat := 4983230072969 + 3 ^ 40 * 2173421 * 2
def baseEnd_2173421 : Nat := 1116009637575646214042125

theorem tailTrace_2173421 : CollatzResearch.WordTrace tailWord_2173421 prefixEnd_2173421 1116009637575646214042125 := by
  unfold tailWord_2173421
  simp only [CollatzResearch.WordTrace]
  refine ⟨79271176259074382599904117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52847450839382921733269411 79271176259074382599904117)
  ·
    refine ⟨7431672774288223368741011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 79271176259074382599904117 7431672774288223368741011)
    ·
      refine ⟨11147509161432335053111517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7431672774288223368741011 11147509161432335053111517)
      ·
        refine ⟨4180315935537125644916819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11147509161432335053111517 4180315935537125644916819)
        ·
          refine ⟨6270473903305688467375229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4180315935537125644916819 6270473903305688467375229)
          ·
            refine ⟨2351427713739633175265711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6270473903305688467375229 2351427713739633175265711)
            ·
              refine ⟨3527141570609449762898567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2351427713739633175265711 3527141570609449762898567)
              ·
                refine ⟨5290712355914174644347851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3527141570609449762898567 5290712355914174644347851)
                ·
                  refine ⟨7936068533871261966521777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5290712355914174644347851 7936068533871261966521777)
                  ·
                    refine ⟨5952051400403446474891333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7936068533871261966521777 5952051400403446474891333)
                    ·
                      refine ⟨1116009637575646214042125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5952051400403446474891333 1116009637575646214042125)
                      ·
                        rfl

theorem cell23_2173421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_2173421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2173421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2173421 prefixEnd_2173421 := by exact prefixLift 2173421
  have htrace : WordTrace (prefixWord ++ tailWord_2173421) baseStart_2173421 baseEnd_2173421 := by
    simpa [prefixWord, tailWord_2173421, baseEnd_2173421] using wordTrace_append hprefix tailTrace_2173421
  have hstable : (prefixWord ++ tailWord_2173421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173421).length < 2 ^ (prefixWord ++ tailWord_2173421).sum := by decide
  have hdescent : baseEnd_2173421 < baseStart_2173421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173451 : List Nat := [1, 1, 1, 1, 7, 1, 2, 3, 1, 3, 2]
def baseStart_2173451 : Nat := 118140960795 + 2173451 * 2 ^ 59
def prefixEnd_2173451 : Nat := 4983230072969 + 3 ^ 40 * 2173451 * 2
def baseEnd_2173451 : Nat := 1116025041995281096666987

theorem tailTrace_2173451 : CollatzResearch.WordTrace tailWord_2173451 prefixEnd_2173451 1116025041995281096666987 := by
  unfold tailWord_2173451
  simp only [CollatzResearch.WordTrace]
  refine ⟨79272270448965697723496207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52848180299310465148997471 79272270448965697723496207)
  ·
    refine ⟨118908405673448546585244311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79272270448965697723496207 118908405673448546585244311)
    ·
      refine ⟨178362608510172819877866467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118908405673448546585244311 178362608510172819877866467)
      ·
        refine ⟨267543912765259229816799701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178362608510172819877866467 267543912765259229816799701)
        ·
          refine ⟨6270560455435763198831243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 267543912765259229816799701 6270560455435763198831243)
          ·
            refine ⟨9405840683153644798246865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6270560455435763198831243 9405840683153644798246865)
            ·
              refine ⟨7054380512365233598685149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9405840683153644798246865 7054380512365233598685149)
              ·
                refine ⟨2645392692136962599506931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7054380512365233598685149 2645392692136962599506931)
                ·
                  refine ⟨3968089038205443899260397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2645392692136962599506931 3968089038205443899260397)
                  ·
                    refine ⟨1488033389327041462222649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3968089038205443899260397 1488033389327041462222649)
                    ·
                      refine ⟨1116025041995281096666987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1488033389327041462222649 1116025041995281096666987)
                      ·
                        rfl

theorem cell23_2173451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 3, 1, 3, 2].length) (baseStart_2173451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2173451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2173451 prefixEnd_2173451 := by exact prefixLift 2173451
  have htrace : WordTrace (prefixWord ++ tailWord_2173451) baseStart_2173451 baseEnd_2173451 := by
    simpa [prefixWord, tailWord_2173451, baseEnd_2173451] using wordTrace_append hprefix tailTrace_2173451
  have hstable : (prefixWord ++ tailWord_2173451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173451).length < 2 ^ (prefixWord ++ tailWord_2173451).sum := by decide
  have hdescent : baseEnd_2173451 < baseStart_2173451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173477 : List Nat := [1, 3, 1, 2, 2, 1, 2, 3, 2, 2, 4]
def baseStart_2173477 : Nat := 118140960795 + 2173477 * 2 ^ 59
def prefixEnd_2173477 : Nat := 4983230072969 + 3 ^ 40 * 2173477 * 2
def baseEnd_2173477 : Nat := 1116038392492297994941867

theorem tailTrace_2173477 : CollatzResearch.WordTrace tailWord_2173477 prefixEnd_2173477 1116038392492297994941867 := by
  unfold tailWord_2173477
  simp only [CollatzResearch.WordTrace]
  refine ⟨79273218746871504163942685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52848812497914336109295123 79273218746871504163942685)
  ·
    refine ⟨29727457030076814061478507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79273218746871504163942685 29727457030076814061478507)
    ·
      refine ⟨44591185545115221092217761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29727457030076814061478507 44591185545115221092217761)
      ·
        refine ⟨33443389158836415819163321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44591185545115221092217761 33443389158836415819163321)
        ·
          refine ⟨25082541869127311864372491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33443389158836415819163321 25082541869127311864372491)
          ·
            refine ⟨37623812803690967796558737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25082541869127311864372491 37623812803690967796558737)
            ·
              refine ⟨28217859602768225847419053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37623812803690967796558737 28217859602768225847419053)
              ·
                refine ⟨10581697351038084692782145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28217859602768225847419053 10581697351038084692782145)
                ·
                  refine ⟨7936273013278563519586609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10581697351038084692782145 7936273013278563519586609)
                  ·
                    refine ⟨5952204759958922639689957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7936273013278563519586609 5952204759958922639689957)
                    ·
                      refine ⟨1116038392492297994941867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5952204759958922639689957 1116038392492297994941867)
                      ·
                        rfl

theorem cell23_2173477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_2173477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2173477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2173477 prefixEnd_2173477 := by exact prefixLift 2173477
  have htrace : WordTrace (prefixWord ++ tailWord_2173477) baseStart_2173477 baseEnd_2173477 := by
    simpa [prefixWord, tailWord_2173477, baseEnd_2173477] using wordTrace_append hprefix tailTrace_2173477
  have hstable : (prefixWord ++ tailWord_2173477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173477).length < 2 ^ (prefixWord ++ tailWord_2173477).sum := by decide
  have hdescent : baseEnd_2173477 < baseStart_2173477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173502 : List Nat := [4, 2, 1, 4, 1, 1, 3, 1, 1, 3, 2]
def baseStart_2173502 : Nat := 118140960795 + 2173502 * 2 ^ 59
def prefixEnd_2173502 : Nat := 4983230072969 + 3 ^ 40 * 2173502 * 2
def baseEnd_2173502 : Nat := 1116051229508660397129253

theorem tailTrace_2173502 : CollatzResearch.WordTrace tailWord_2173502 prefixEnd_2173502 1116051229508660397129253 := by
  unfold tailWord_2173502
  simp only [CollatzResearch.WordTrace]
  refine ⟨9909266321472616679200345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52849420381187288955735173 9909266321472616679200345)
  ·
    refine ⟨7431949741104462509400259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9909266321472616679200345 7431949741104462509400259)
    ·
      refine ⟨11147924611656693764100389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7431949741104462509400259 11147924611656693764100389)
      ·
        refine ⟨2090235864685630080768823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11147924611656693764100389 2090235864685630080768823)
        ·
          refine ⟨3135353797028445121153235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2090235864685630080768823 3135353797028445121153235)
          ·
            refine ⟨4703030695542667681729853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3135353797028445121153235 4703030695542667681729853)
            ·
              refine ⟨1763636510828500380648695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4703030695542667681729853 1763636510828500380648695)
              ·
                refine ⟨2645454766242750570973043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1763636510828500380648695 2645454766242750570973043)
                ·
                  refine ⟨3968182149364125856459565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2645454766242750570973043 3968182149364125856459565)
                  ·
                    refine ⟨1488068306011547196172337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3968182149364125856459565 1488068306011547196172337)
                    ·
                      refine ⟨1116051229508660397129253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1488068306011547196172337 1116051229508660397129253)
                      ·
                        rfl

theorem cell23_2173502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_2173502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2173502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2173502 prefixEnd_2173502 := by exact prefixLift 2173502
  have htrace : WordTrace (prefixWord ++ tailWord_2173502) baseStart_2173502 baseEnd_2173502 := by
    simpa [prefixWord, tailWord_2173502, baseEnd_2173502] using wordTrace_append hprefix tailTrace_2173502
  have hstable : (prefixWord ++ tailWord_2173502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173502).length < 2 ^ (prefixWord ++ tailWord_2173502).sum := by decide
  have hdescent : baseEnd_2173502 < baseStart_2173502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173521 : List Nat := [1, 2, 2, 1, 3, 3, 4, 2, 5]
def baseStart_2173521 : Nat := 118140960795 + 2173521 * 2 ^ 59
def prefixEnd_2173521 : Nat := 4983230072969 + 3 ^ 40 * 2173521 * 2
def baseEnd_2173521 : Nat := 124006776182343980310185

theorem tailTrace_2173521 : CollatzResearch.WordTrace tailWord_2173521 prefixEnd_2173521 124006776182343980310185 := by
  unfold tailWord_2173521
  simp only [CollatzResearch.WordTrace]
  refine ⟨79274823558712099678544417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52849882372474733119029611 79274823558712099678544417)
  ·
    refine ⟨59456117669034074758908313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79274823558712099678544417 59456117669034074758908313)
    ·
      refine ⟨44592088251775556069181235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59456117669034074758908313 44592088251775556069181235)
      ·
        refine ⟨66888132377663334103771853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44592088251775556069181235 66888132377663334103771853)
        ·
          refine ⟨25083049641623750288914445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66888132377663334103771853 25083049641623750288914445)
          ·
            refine ⟨9406143615608906358342917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25083049641623750288914445 9406143615608906358342917)
            ·
              refine ⟨1763651927926669942189297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9406143615608906358342917 1763651927926669942189297)
              ·
                refine ⟨1322738945945002456641973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1763651927926669942189297 1322738945945002456641973)
                ·
                  refine ⟨124006776182343980310185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1322738945945002456641973 124006776182343980310185)
                  ·
                    rfl

theorem cell23_2173521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 2, 5].length) (baseStart_2173521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2173521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2173521 prefixEnd_2173521 := by exact prefixLift 2173521
  have htrace : WordTrace (prefixWord ++ tailWord_2173521) baseStart_2173521 baseEnd_2173521 := by
    simpa [prefixWord, tailWord_2173521, baseEnd_2173521] using wordTrace_append hprefix tailTrace_2173521
  have hstable : (prefixWord ++ tailWord_2173521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173521).length < 2 ^ (prefixWord ++ tailWord_2173521).sum := by decide
  have hdescent : baseEnd_2173521 < baseStart_2173521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173527 : List Nat := [1, 1, 3, 2, 2, 2, 1, 3, 1, 2, 5]
def baseStart_2173527 : Nat := 118140960795 + 2173527 * 2 ^ 59
def prefixEnd_2173527 : Nat := 4983230072969 + 3 ^ 40 * 2173527 * 2
def baseEnd_2173527 : Nat := 1116064066525022799316637

theorem tailTrace_2173527 : CollatzResearch.WordTrace tailWord_2173527 prefixEnd_2173527 1116064066525022799316637 := by
  unfold tailWord_2173527
  simp only [CollatzResearch.WordTrace]
  refine ⟨79275042396690362703262835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52850028264460241802175223 79275042396690362703262835)
  ·
    refine ⟨118912563595035544054894253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79275042396690362703262835 118912563595035544054894253)
    ·
      refine ⟨44592211348138329020585345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118912563595035544054894253 44592211348138329020585345)
      ·
        refine ⟨33444158511103746765439009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44592211348138329020585345 33444158511103746765439009)
        ·
          refine ⟨25083118883327810074079257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33444158511103746765439009 25083118883327810074079257)
          ·
            refine ⟨18812339162495857555559443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25083118883327810074079257 18812339162495857555559443)
            ·
              refine ⟨28218508743743786333339165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18812339162495857555559443 28218508743743786333339165)
              ·
                refine ⟨10581940778903919875002187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28218508743743786333339165 10581940778903919875002187)
                ·
                  refine ⟨15872911168355879812503281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10581940778903919875002187 15872911168355879812503281)
                  ·
                    refine ⟨11904683376266909859377461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15872911168355879812503281 11904683376266909859377461)
                    ·
                      refine ⟨1116064066525022799316637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11904683376266909859377461 1116064066525022799316637)
                      ·
                        rfl

theorem cell23_2173527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_2173527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2173527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2173527 prefixEnd_2173527 := by exact prefixLift 2173527
  have htrace : WordTrace (prefixWord ++ tailWord_2173527) baseStart_2173527 baseEnd_2173527 := by
    simpa [prefixWord, tailWord_2173527, baseEnd_2173527] using wordTrace_append hprefix tailTrace_2173527
  have hstable : (prefixWord ++ tailWord_2173527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173527).length < 2 ^ (prefixWord ++ tailWord_2173527).sum := by decide
  have hdescent : baseEnd_2173527 < baseStart_2173527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173588 : List Nat := [2, 4, 2, 2, 1, 1, 2, 1, 2, 4, 2]
def baseStart_2173588 : Nat := 118140960795 + 2173588 * 2 ^ 59
def prefixEnd_2173588 : Nat := 4983230072969 + 3 ^ 40 * 2173588 * 2
def baseEnd_2173588 : Nat := 1116095388844947060653857

theorem tailTrace_2173588 : CollatzResearch.WordTrace tailWord_2173588 prefixEnd_2173588 1116095388844947060653857 := by
  unfold tailWord_2173588
  simp only [CollatzResearch.WordTrace]
  refine ⟨39638633624734685060616709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52851511499646246747488945 39638633624734685060616709)
  ·
    refine ⟨7432243804637753448865633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39638633624734685060616709 7432243804637753448865633)
    ·
      refine ⟨5574182853478315086649225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7432243804637753448865633 5574182853478315086649225)
      ·
        refine ⟨4180637140108736314986919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5574182853478315086649225 4180637140108736314986919)
        ·
          refine ⟨6270955710163104472480379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4180637140108736314986919 6270955710163104472480379)
          ·
            refine ⟨9406433565244656708720569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6270955710163104472480379 9406433565244656708720569)
            ·
              refine ⟨7054825173933492531540427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9406433565244656708720569 7054825173933492531540427)
              ·
                refine ⟨10582237760900238797310641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7054825173933492531540427 10582237760900238797310641)
                ·
                  refine ⟨7936678320675179097982981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10582237760900238797310641 7936678320675179097982981)
                  ·
                    refine ⟨1488127185126596080871809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7936678320675179097982981 1488127185126596080871809)
                    ·
                      refine ⟨1116095388844947060653857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1488127185126596080871809 1116095388844947060653857)
                      ·
                        rfl

theorem cell23_2173588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_2173588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2173588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2173588 prefixEnd_2173588 := by exact prefixLift 2173588
  have htrace : WordTrace (prefixWord ++ tailWord_2173588) baseStart_2173588 baseEnd_2173588 := by
    simpa [prefixWord, tailWord_2173588, baseEnd_2173588] using wordTrace_append hprefix tailTrace_2173588
  have hstable : (prefixWord ++ tailWord_2173588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173588).length < 2 ^ (prefixWord ++ tailWord_2173588).sum := by decide
  have hdescent : baseEnd_2173588 < baseStart_2173588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173604 : List Nat := [2, 3, 1, 2, 2, 1, 1, 1, 2, 5, 3]
def baseStart_2173604 : Nat := 118140960795 + 2173604 * 2 ^ 59
def prefixEnd_2173604 : Nat := 4983230072969 + 3 ^ 40 * 2173604 * 2
def baseEnd_2173604 : Nat := 1116103604535418998053783

theorem tailTrace_2173604 : CollatzResearch.WordTrace tailWord_2173604 prefixEnd_2173604 1116103604535418998053783 := by
  unfold tailWord_2173604
  simp only [CollatzResearch.WordTrace]
  refine ⟨39638925408705702426907933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52851900544940936569210577 39638925408705702426907933)
  ·
    refine ⟨14864597028264638410090475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39638925408705702426907933 14864597028264638410090475)
    ·
      refine ⟨22296895542396957615135713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14864597028264638410090475 22296895542396957615135713)
      ·
        refine ⟨16722671656797718211351785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22296895542396957615135713 16722671656797718211351785)
        ·
          refine ⟨12542003742598288658513839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16722671656797718211351785 12542003742598288658513839)
          ·
            refine ⟨18813005613897432987770759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12542003742598288658513839 18813005613897432987770759)
            ·
              refine ⟨28219508420846149481656139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18813005613897432987770759 28219508420846149481656139)
              ·
                refine ⟨42329262631269224222484209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28219508420846149481656139 42329262631269224222484209)
                ·
                  refine ⟨31746946973451918166863157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42329262631269224222484209 31746946973451918166863157)
                  ·
                    refine ⟨2976276278761117328143421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31746946973451918166863157 2976276278761117328143421)
                    ·
                      refine ⟨1116103604535418998053783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2976276278761117328143421 1116103604535418998053783)
                      ·
                        rfl

theorem cell23_2173604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_2173604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2173604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2173604 prefixEnd_2173604 := by exact prefixLift 2173604
  have htrace : WordTrace (prefixWord ++ tailWord_2173604) baseStart_2173604 baseEnd_2173604 := by
    simpa [prefixWord, tailWord_2173604, baseEnd_2173604] using wordTrace_append hprefix tailTrace_2173604
  have hstable : (prefixWord ++ tailWord_2173604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173604).length < 2 ^ (prefixWord ++ tailWord_2173604).sum := by decide
  have hdescent : baseEnd_2173604 < baseStart_2173604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173631 : List Nat := [1, 1, 2, 2, 2, 4, 1, 1, 4, 3, 2]
def baseStart_2173631 : Nat := 118140960795 + 2173631 * 2 ^ 59
def prefixEnd_2173631 : Nat := 4983230072969 + 3 ^ 40 * 2173631 * 2
def baseEnd_2173631 : Nat := 1116117468513090392416159

theorem tailTrace_2173631 : CollatzResearch.WordTrace tailWord_2173631 prefixEnd_2173631 1116117468513090392416159 := by
  unfold tailWord_2173631
  simp only [CollatzResearch.WordTrace]
  refine ⟨79278835588313588465048747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52852557058875725643365831 79278835588313588465048747)
  ·
    refine ⟨118918253382470382697573121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79278835588313588465048747 118918253382470382697573121)
    ·
      refine ⟨89188690036852787023179841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118918253382470382697573121 89188690036852787023179841)
      ·
        refine ⟨66891517527639590267384881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89188690036852787023179841 66891517527639590267384881)
        ·
          refine ⟨50168638145729692700538661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66891517527639590267384881 50168638145729692700538661)
          ·
            refine ⟨9406619652324317381350999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50168638145729692700538661 9406619652324317381350999)
            ·
              refine ⟨14109929478486476072026499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9406619652324317381350999 14109929478486476072026499)
              ·
                refine ⟨21164894217729714108039749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14109929478486476072026499 21164894217729714108039749)
                ·
                  refine ⟨3968417665824321395257453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21164894217729714108039749 3968417665824321395257453)
                  ·
                    refine ⟨1488156624684120523221545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3968417665824321395257453 1488156624684120523221545)
                    ·
                      refine ⟨1116117468513090392416159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1488156624684120523221545 1116117468513090392416159)
                      ·
                        rfl

theorem cell23_2173631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 4, 3, 2].length) (baseStart_2173631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2173631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2173631 prefixEnd_2173631 := by exact prefixLift 2173631
  have htrace : WordTrace (prefixWord ++ tailWord_2173631) baseStart_2173631 baseEnd_2173631 := by
    simpa [prefixWord, tailWord_2173631, baseEnd_2173631] using wordTrace_append hprefix tailTrace_2173631
  have hstable : (prefixWord ++ tailWord_2173631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173631).length < 2 ^ (prefixWord ++ tailWord_2173631).sum := by decide
  have hdescent : baseEnd_2173631 < baseStart_2173631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173637 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 2, 10]
def baseStart_2173637 : Nat := 118140960795 + 2173637 * 2 ^ 59
def prefixEnd_2173637 : Nat := 4983230072969 + 3 ^ 40 * 2173637 * 2
def baseEnd_2173637 : Nat := 372040183132339122980377

theorem tailTrace_2173637 : CollatzResearch.WordTrace tailWord_2173637 prefixEnd_2173637 372040183132339122980377 := by
  unfold tailWord_2173637
  simp only [CollatzResearch.WordTrace]
  refine ⟨79279054426291851489767165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52852702950861234326511443 79279054426291851489767165)
  ·
    refine ⟨29729645409859444308662687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79279054426291851489767165 29729645409859444308662687)
    ·
      refine ⟨44594468114789166462994031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29729645409859444308662687 44594468114789166462994031)
      ·
        refine ⟨66891702172183749694491047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44594468114789166462994031 66891702172183749694491047)
        ·
          refine ⟨100337553258275624541736571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66891702172183749694491047 100337553258275624541736571)
          ·
            refine ⟨150506329887413436812604857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100337553258275624541736571 150506329887413436812604857)
            ·
              refine ⟨112879747415560077609453643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150506329887413436812604857 112879747415560077609453643)
              ·
                refine ⟨169319621123340116414180465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112879747415560077609453643 169319621123340116414180465)
                ·
                  refine ⟨126989715842505087310635349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 169319621123340116414180465 126989715842505087310635349)
                  ·
                    refine ⟨372040183132339122980377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 126989715842505087310635349 372040183132339122980377)
                    ·
                      rfl

theorem cell23_2173637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 10].length) (baseStart_2173637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2173637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2173637 prefixEnd_2173637 := by exact prefixLift 2173637
  have htrace : WordTrace (prefixWord ++ tailWord_2173637) baseStart_2173637 baseEnd_2173637 := by
    simpa [prefixWord, tailWord_2173637, baseEnd_2173637] using wordTrace_append hprefix tailTrace_2173637
  have hstable : (prefixWord ++ tailWord_2173637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173637).length < 2 ^ (prefixWord ++ tailWord_2173637).sum := by decide
  have hdescent : baseEnd_2173637 < baseStart_2173637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173698 : List Nat := [3, 4, 1, 1, 1, 2, 1, 2, 3, 2, 3]
def baseStart_2173698 : Nat := 118140960795 + 2173698 * 2 ^ 59
def prefixEnd_2173698 : Nat := 4983230072969 + 3 ^ 40 * 2173698 * 2
def baseEnd_2173698 : Nat := 1116151871716941630278351

theorem tailTrace_2173698 : CollatzResearch.WordTrace tailWord_2173698 prefixEnd_2173698 1116151871716941630278351 := by
  unfold tailWord_2173698
  simp only [CollatzResearch.WordTrace]
  refine ⟨19820319819767714726934437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52854186186047239271825165 19820319819767714726934437)
  ·
    refine ⟨3716309966206446511300207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19820319819767714726934437 3716309966206446511300207)
    ·
      refine ⟨5574464949309669766950311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3716309966206446511300207 5574464949309669766950311)
      ·
        refine ⟨8361697423964504650425467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5574464949309669766950311 8361697423964504650425467)
        ·
          refine ⟨12542546135946756975638201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8361697423964504650425467 12542546135946756975638201)
          ·
            refine ⟨9406909601960067731728651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12542546135946756975638201 9406909601960067731728651)
            ·
              refine ⟨14110364402940101597592977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9406909601960067731728651 14110364402940101597592977)
              ·
                refine ⟨10582773302205076198194733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14110364402940101597592977 10582773302205076198194733)
                ·
                  refine ⟨3968539988326903574323025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10582773302205076198194733 3968539988326903574323025)
                  ·
                    refine ⟨2976404991245177680742269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3968539988326903574323025 2976404991245177680742269)
                    ·
                      refine ⟨1116151871716941630278351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2976404991245177680742269 1116151871716941630278351)
                      ·
                        rfl

theorem cell23_2173698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_2173698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2173698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2173698 prefixEnd_2173698 := by exact prefixLift 2173698
  have htrace : WordTrace (prefixWord ++ tailWord_2173698) baseStart_2173698 baseEnd_2173698 := by
    simpa [prefixWord, tailWord_2173698, baseEnd_2173698] using wordTrace_append hprefix tailTrace_2173698
  have hstable : (prefixWord ++ tailWord_2173698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173698).length < 2 ^ (prefixWord ++ tailWord_2173698).sum := by decide
  have hdescent : baseEnd_2173698 < baseStart_2173698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173711 : List Nat := [1, 1, 2, 1, 1, 1, 8, 1, 1, 3, 3]
def baseStart_2173711 : Nat := 118140960795 + 2173711 * 2 ^ 59
def prefixEnd_2173711 : Nat := 4983230072969 + 3 ^ 40 * 2173711 * 2
def baseEnd_2173711 : Nat := 1116158546965450079415791

theorem tailTrace_2173711 : CollatzResearch.WordTrace tailWord_2173711 prefixEnd_2173711 1116158546965450079415791 := by
  unfold tailWord_2173711
  simp only [CollatzResearch.WordTrace]
  refine ⟨79281753428023762127960987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52854502285349174751973991 79281753428023762127960987)
  ·
    refine ⟨118922630142035643191941481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79281753428023762127960987 118922630142035643191941481)
    ·
      refine ⟨89191972606526732393956111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118922630142035643191941481 89191972606526732393956111)
      ·
        refine ⟨133787958909790098590934167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89191972606526732393956111 133787958909790098590934167)
        ·
          refine ⟨200681938364685147886401251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133787958909790098590934167 200681938364685147886401251)
          ·
            refine ⟨301022907547027721829601877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200681938364685147886401251 301022907547027721829601877)
            ·
              refine ⟨3527612197816731115190647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 301022907547027721829601877 3527612197816731115190647)
              ·
                refine ⟨5291418296725096672785971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3527612197816731115190647 5291418296725096672785971)
                ·
                  refine ⟨7937127445087645009178957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5291418296725096672785971 7937127445087645009178957)
                  ·
                    refine ⟨2976422791907866878442109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7937127445087645009178957 2976422791907866878442109)
                    ·
                      refine ⟨1116158546965450079415791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2976422791907866878442109 1116158546965450079415791)
                      ·
                        rfl

theorem cell23_2173711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 1, 1, 3, 3].length) (baseStart_2173711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2173711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2173711 prefixEnd_2173711 := by exact prefixLift 2173711
  have htrace : WordTrace (prefixWord ++ tailWord_2173711) baseStart_2173711 baseEnd_2173711 := by
    simpa [prefixWord, tailWord_2173711, baseEnd_2173711] using wordTrace_append hprefix tailTrace_2173711
  have hstable : (prefixWord ++ tailWord_2173711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173711).length < 2 ^ (prefixWord ++ tailWord_2173711).sum := by decide
  have hdescent : baseEnd_2173711 < baseStart_2173711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173732 : List Nat := [2, 3, 1, 3, 3, 2, 2, 1, 1, 2, 3]
def baseStart_2173732 : Nat := 118140960795 + 2173732 * 2 ^ 59
def prefixEnd_2173732 : Nat := 4983230072969 + 3 ^ 40 * 2173732 * 2
def baseEnd_2173732 : Nat := 1116169330059194497253195

theorem tailTrace_2173732 : CollatzResearch.WordTrace tailWord_2173732 prefixEnd_2173732 1116169330059194497253195 := by
  unfold tailWord_2173732
  simp only [CollatzResearch.WordTrace]
  refine ⟨39641259680473841357237725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52855012907298455142983633 39641259680473841357237725)
  ·
    refine ⟨14865472380177690508964147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39641259680473841357237725 14865472380177690508964147)
    ·
      refine ⟨22298208570266535763446221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14865472380177690508964147 22298208570266535763446221)
      ·
        refine ⟨8361828213849950911292333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22298208570266535763446221 8361828213849950911292333)
        ·
          refine ⟨3135685580193731591734625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8361828213849950911292333 3135685580193731591734625)
          ·
            refine ⟨2351764185145298693800969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3135685580193731591734625 2351764185145298693800969)
            ·
              refine ⟨1763823138858974020350727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2351764185145298693800969 1763823138858974020350727)
              ·
                refine ⟨2645734708288461030526091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1763823138858974020350727 2645734708288461030526091)
                ·
                  refine ⟨3968602062432691545789137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2645734708288461030526091 3968602062432691545789137)
                  ·
                    refine ⟨2976451546824518659341853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3968602062432691545789137 2976451546824518659341853)
                    ·
                      refine ⟨1116169330059194497253195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2976451546824518659341853 1116169330059194497253195)
                      ·
                        rfl

theorem cell23_2173732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_2173732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2173732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2173732 prefixEnd_2173732 := by exact prefixLift 2173732
  have htrace : WordTrace (prefixWord ++ tailWord_2173732) baseStart_2173732 baseEnd_2173732 := by
    simpa [prefixWord, tailWord_2173732, baseEnd_2173732] using wordTrace_append hprefix tailTrace_2173732
  have hstable : (prefixWord ++ tailWord_2173732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173732).length < 2 ^ (prefixWord ++ tailWord_2173732).sum := by decide
  have hdescent : baseEnd_2173732 < baseStart_2173732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173788 : List Nat := [2, 2, 4, 2, 1, 2, 1, 1, 2, 1, 5]
def baseStart_2173788 : Nat := 118140960795 + 2173788 * 2 ^ 59
def prefixEnd_2173788 : Nat := 4983230072969 + 3 ^ 40 * 2173788 * 2
def baseEnd_2173788 : Nat := 1116198084975846278152937

theorem tailTrace_2173788 : CollatzResearch.WordTrace tailWord_2173788 prefixEnd_2173788 1116198084975846278152937 := by
  unfold tailWord_2173788
  simp only [CollatzResearch.WordTrace]
  refine ⟨39642280924372402139257009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52856374565829869519009345 39642280924372402139257009)
  ·
    refine ⟨29731710693279301604442757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39642280924372402139257009 29731710693279301604442757)
    ·
      refine ⟨5574695754989869050833017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29731710693279301604442757 5574695754989869050833017)
      ·
        refine ⟨4181021816242401788124763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5574695754989869050833017 4181021816242401788124763)
        ·
          refine ⟨6271532724363602682187145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4181021816242401788124763 6271532724363602682187145)
          ·
            refine ⟨4703649543272702011640359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6271532724363602682187145 4703649543272702011640359)
            ·
              refine ⟨7055474314909053017460539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4703649543272702011640359 7055474314909053017460539)
              ·
                refine ⟨10583211472363579526190809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7055474314909053017460539 10583211472363579526190809)
                ·
                  refine ⟨7937408604272684644643107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10583211472363579526190809 7937408604272684644643107)
                  ·
                    refine ⟨11906112906409026966964661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7937408604272684644643107 11906112906409026966964661)
                    ·
                      refine ⟨1116198084975846278152937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11906112906409026966964661 1116198084975846278152937)
                      ·
                        rfl

theorem cell23_2173788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_2173788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2173788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2173788 prefixEnd_2173788 := by exact prefixLift 2173788
  have htrace : WordTrace (prefixWord ++ tailWord_2173788) baseStart_2173788 baseEnd_2173788 := by
    simpa [prefixWord, tailWord_2173788, baseEnd_2173788] using wordTrace_append hprefix tailTrace_2173788
  have hstable : (prefixWord ++ tailWord_2173788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173788).length < 2 ^ (prefixWord ++ tailWord_2173788).sum := by decide
  have hdescent : baseEnd_2173788 < baseStart_2173788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173861 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 5, 4, 3]
def baseStart_2173861 : Nat := 118140960795 + 2173861 * 2 ^ 59
def prefixEnd_2173861 : Nat := 4983230072969 + 3 ^ 40 * 2173861 * 2
def baseEnd_2173861 : Nat := 1116235569063624492540101

theorem tailTrace_2173861 : CollatzResearch.WordTrace tailWord_2173861 prefixEnd_2173861 1116235569063624492540101 := by
  unfold tailWord_2173861
  simp only [CollatzResearch.WordTrace]
  refine ⟨79287224377480337745921437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52858149584986891830614291 79287224377480337745921437)
  ·
    refine ⟨29732709141555126654720539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79287224377480337745921437 29732709141555126654720539)
    ·
      refine ⟨44599063712332689982080809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29732709141555126654720539 44599063712332689982080809)
      ·
        refine ⟨33449297784249517486560607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44599063712332689982080809 33449297784249517486560607)
        ·
          refine ⟨50173946676374276229840911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33449297784249517486560607 50173946676374276229840911)
          ·
            refine ⟨75260920014561414344761367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50173946676374276229840911 75260920014561414344761367)
            ·
              refine ⟨112891380021842121517142051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75260920014561414344761367 112891380021842121517142051)
              ·
                refine ⟨169337070032763182275713077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112891380021842121517142051 169337070032763182275713077)
                ·
                  refine ⟨15875350315571548338348101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 169337070032763182275713077 15875350315571548338348101)
                  ·
                    refine ⟨2976628184169665313440269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15875350315571548338348101 2976628184169665313440269)
                    ·
                      refine ⟨1116235569063624492540101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2976628184169665313440269 1116235569063624492540101)
                      ·
                        rfl

theorem cell23_2173861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 4, 3].length) (baseStart_2173861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2173861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2173861 prefixEnd_2173861 := by exact prefixLift 2173861
  have htrace : WordTrace (prefixWord ++ tailWord_2173861) baseStart_2173861 baseEnd_2173861 := by
    simpa [prefixWord, tailWord_2173861, baseEnd_2173861] using wordTrace_append hprefix tailTrace_2173861
  have hstable : (prefixWord ++ tailWord_2173861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173861).length < 2 ^ (prefixWord ++ tailWord_2173861).sum := by decide
  have hdescent : baseEnd_2173861 < baseStart_2173861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173885 : List Nat := [1, 4, 1, 2, 4, 1, 1, 2, 3, 4]
def baseStart_2173885 : Nat := 118140960795 + 2173885 * 2 ^ 59
def prefixEnd_2173885 : Nat := 4983230072969 + 3 ^ 40 * 2173885 * 2
def baseEnd_2173885 : Nat := 372082630866444132879997

theorem tailTrace_2173885 : CollatzResearch.WordTrace tailWord_2173885 prefixEnd_2173885 372082630866444132879997 := by
  unfold tailWord_2173885
  simp only [CollatzResearch.WordTrace]
  refine ⟨79288099729393389844795109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52858733152928926563196739 79288099729393389844795109)
  ·
    refine ⟨14866518699261260595899083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79288099729393389844795109 14866518699261260595899083)
    ·
      refine ⟨22299778048891890893848625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14866518699261260595899083 22299778048891890893848625)
      ·
        refine ⟨16724833536668918170386469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22299778048891890893848625 16724833536668918170386469)
        ·
          refine ⟨3135906288125422156947463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16724833536668918170386469 3135906288125422156947463)
          ·
            refine ⟨4703859432188133235421195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3135906288125422156947463 4703859432188133235421195)
            ·
              refine ⟨7055789148282199853131793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4703859432188133235421195 7055789148282199853131793)
              ·
                refine ⟨5291841861211649889848845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7055789148282199853131793 5291841861211649889848845)
                ·
                  refine ⟨1984440697954368708693317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5291841861211649889848845 1984440697954368708693317)
                  ·
                    refine ⟨372082630866444132879997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1984440697954368708693317 372082630866444132879997)
                    ·
                      rfl

theorem cell23_2173885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 2, 3, 4].length) (baseStart_2173885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2173885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2173885 prefixEnd_2173885 := by exact prefixLift 2173885
  have htrace : WordTrace (prefixWord ++ tailWord_2173885) baseStart_2173885 baseEnd_2173885 := by
    simpa [prefixWord, tailWord_2173885, baseEnd_2173885] using wordTrace_append hprefix tailTrace_2173885
  have hstable : (prefixWord ++ tailWord_2173885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173885).length < 2 ^ (prefixWord ++ tailWord_2173885).sum := by decide
  have hdescent : baseEnd_2173885 < baseStart_2173885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173891 : List Nat := [1, 1, 1, 3, 1, 1, 2, 3, 2, 5, 3]
def baseStart_2173891 : Nat := 118140960795 + 2173891 * 2 ^ 59
def prefixEnd_2173891 : Nat := 4983230072969 + 3 ^ 40 * 2173891 * 2
def baseEnd_2173891 : Nat := 1116250973483259375164963

theorem tailTrace_2173891 : CollatzResearch.WordTrace tailWord_2173891 prefixEnd_2173891 1116250973483259375164963 := by
  unfold tailWord_2173891
  simp only [CollatzResearch.WordTrace]
  refine ⟨79288318567371652869513527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52858879044914435246342351 79288318567371652869513527)
  ·
    refine ⟨118932477851057479304270291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79288318567371652869513527 118932477851057479304270291)
    ·
      refine ⟨178398716776586218956405437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118932477851057479304270291 178398716776586218956405437)
      ·
        refine ⟨66899518791219832108652039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 178398716776586218956405437 66899518791219832108652039)
        ·
          refine ⟨100349278186829748162978059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66899518791219832108652039 100349278186829748162978059)
          ·
            refine ⟨150523917280244622244467089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100349278186829748162978059 150523917280244622244467089)
            ·
              refine ⟨112892937960183466683350317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150523917280244622244467089 112892937960183466683350317)
              ·
                refine ⟨42334851735068800006256369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 112892937960183466683350317 42334851735068800006256369)
                ·
                  refine ⟨31751138801301600004692277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42334851735068800006256369 31751138801301600004692277)
                  ·
                    refine ⟨2976669262622025000439901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31751138801301600004692277 2976669262622025000439901)
                    ·
                      refine ⟨1116250973483259375164963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2976669262622025000439901 1116250973483259375164963)
                      ·
                        rfl

theorem cell23_2173891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 5, 3].length) (baseStart_2173891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2173891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2173891 prefixEnd_2173891 := by exact prefixLift 2173891
  have htrace : WordTrace (prefixWord ++ tailWord_2173891) baseStart_2173891 baseEnd_2173891 := by
    simpa [prefixWord, tailWord_2173891, baseEnd_2173891] using wordTrace_append hprefix tailTrace_2173891
  have hstable : (prefixWord ++ tailWord_2173891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173891).length < 2 ^ (prefixWord ++ tailWord_2173891).sum := by decide
  have hdescent : baseEnd_2173891 < baseStart_2173891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173902 : List Nat := [4, 1, 1, 1, 2, 4, 2, 3, 1, 4]
def baseStart_2173902 : Nat := 118140960795 + 2173902 * 2 ^ 59
def prefixEnd_2173902 : Nat := 4983230072969 + 3 ^ 40 * 2173902 * 2
def baseEnd_2173902 : Nat := 372085540590152944042471

theorem tailTrace_2173902 : CollatzResearch.WordTrace tailWord_2173902 prefixEnd_2173902 372085540590152944042471 := by
  unfold tailWord_2173902
  simp only [CollatzResearch.WordTrace]
  refine ⟨9911089971291475218520495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52859146513554534498775973 9911089971291475218520495)
  ·
    refine ⟨14866634956937212827780743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9911089971291475218520495 14866634956937212827780743)
    ·
      refine ⟨22299952435405819241671115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14866634956937212827780743 22299952435405819241671115)
      ·
        refine ⟨33449928653108728862506673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22299952435405819241671115 33449928653108728862506673)
        ·
          refine ⟨25087446489831546646880005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33449928653108728862506673 25087446489831546646880005)
          ·
            refine ⟨4703896216843414996290001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25087446489831546646880005 4703896216843414996290001)
            ·
              refine ⟨3527922162632561247217501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4703896216843414996290001 3527922162632561247217501)
              ·
                refine ⟨1322970810987210467706563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3527922162632561247217501 1322970810987210467706563)
                ·
                  refine ⟨1984456216480815701559845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1322970810987210467706563 1984456216480815701559845)
                  ·
                    refine ⟨372085540590152944042471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1984456216480815701559845 372085540590152944042471)
                    ·
                      rfl

theorem cell23_2173902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 3, 1, 4].length) (baseStart_2173902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2173902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2173902 prefixEnd_2173902 := by exact prefixLift 2173902
  have htrace : WordTrace (prefixWord ++ tailWord_2173902) baseStart_2173902 baseEnd_2173902 := by
    simpa [prefixWord, tailWord_2173902, baseEnd_2173902] using wordTrace_append hprefix tailTrace_2173902
  have hstable : (prefixWord ++ tailWord_2173902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173902).length < 2 ^ (prefixWord ++ tailWord_2173902).sum := by decide
  have hdescent : baseEnd_2173902 < baseStart_2173902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173911 : List Nat := [1, 1, 3, 2, 1, 1, 2, 2, 5, 5]
def baseStart_2173911 : Nat := 118140960795 + 2173911 * 2 ^ 59
def prefixEnd_2173911 : Nat := 4983230072969 + 3 ^ 40 * 2173911 * 2
def baseEnd_2173911 : Nat := 372087081032116432304957

theorem tailTrace_2173911 : CollatzResearch.WordTrace tailWord_2173911 prefixEnd_2173911 372087081032116432304957 := by
  unfold tailWord_2173911
  simp only [CollatzResearch.WordTrace]
  refine ⟨79289048027299196285241587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52859365351532797523494391 79289048027299196285241587)
  ·
    refine ⟨118933572040948794427862381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79289048027299196285241587 118933572040948794427862381)
    ·
      refine ⟨44600089515355797910448393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118933572040948794427862381 44600089515355797910448393)
      ·
        refine ⟨33450067136516848432836295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44600089515355797910448393 33450067136516848432836295)
        ·
          refine ⟨50175100704775272649254443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33450067136516848432836295 50175100704775272649254443)
          ·
            refine ⟨75262651057162908973881665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50175100704775272649254443 75262651057162908973881665)
            ·
              refine ⟨56446988292872181730411249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75262651057162908973881665 56446988292872181730411249)
              ·
                refine ⟨42335241219654136297808437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56446988292872181730411249 42335241219654136297808437)
                ·
                  refine ⟨3968928864342575277919541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42335241219654136297808437 3968928864342575277919541)
                  ·
                    refine ⟨372087081032116432304957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3968928864342575277919541 372087081032116432304957)
                    ·
                      rfl

theorem cell23_2173911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 5, 5].length) (baseStart_2173911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2173911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2173911 prefixEnd_2173911 := by exact prefixLift 2173911
  have htrace : WordTrace (prefixWord ++ tailWord_2173911) baseStart_2173911 baseEnd_2173911 := by
    simpa [prefixWord, tailWord_2173911, baseEnd_2173911] using wordTrace_append hprefix tailTrace_2173911
  have hstable : (prefixWord ++ tailWord_2173911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173911).length < 2 ^ (prefixWord ++ tailWord_2173911).sum := by decide
  have hdescent : baseEnd_2173911 < baseStart_2173911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173942 : List Nat := [5, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3]
def baseStart_2173942 : Nat := 118140960795 + 2173942 * 2 ^ 59
def prefixEnd_2173942 : Nat := 4983230072969 + 3 ^ 40 * 2173942 * 2
def baseEnd_2173942 : Nat := 1116277160996638675627229

theorem tailTrace_2173942 : CollatzResearch.WordTrace tailWord_2173942 prefixEnd_2173942 1116277160996638675627229 := by
  unfold tailWord_2173942
  simp only [CollatzResearch.WordTrace]
  refine ⟨4955636168136680536226255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52860119126791259053080053 4955636168136680536226255)
  ·
    refine ⟨7433454252205020804339383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4955636168136680536226255 7433454252205020804339383)
    ·
      refine ⟨11150181378307531206509075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7433454252205020804339383 11150181378307531206509075)
      ·
        refine ⟨16725272067461296809763613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11150181378307531206509075 16725272067461296809763613)
        ·
          refine ⟨6271977025297986303661355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16725272067461296809763613 6271977025297986303661355)
          ·
            refine ⟨9407965537946979455492033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6271977025297986303661355 9407965537946979455492033)
            ·
              refine ⟨7055974153460234591619025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9407965537946979455492033 7055974153460234591619025)
              ·
                refine ⟨5291980615095175943714269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7055974153460234591619025 5291980615095175943714269)
                ·
                  refine ⟨1984492730660690978892851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5291980615095175943714269 1984492730660690978892851)
                  ·
                    refine ⟨2976739095991036468339277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1984492730660690978892851 2976739095991036468339277)
                    ·
                      refine ⟨1116277160996638675627229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2976739095991036468339277 1116277160996638675627229)
                      ·
                        rfl

theorem cell23_2173942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3].length) (baseStart_2173942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2173942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2173942 prefixEnd_2173942 := by exact prefixLift 2173942
  have htrace : WordTrace (prefixWord ++ tailWord_2173942) baseStart_2173942 baseEnd_2173942 := by
    simpa [prefixWord, tailWord_2173942, baseEnd_2173942] using wordTrace_append hprefix tailTrace_2173942
  have hstable : (prefixWord ++ tailWord_2173942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173942).length < 2 ^ (prefixWord ++ tailWord_2173942).sum := by decide
  have hdescent : baseEnd_2173942 < baseStart_2173942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173975 : List Nat := [1, 1, 3, 5, 1, 1, 2, 1, 4, 4]
def baseStart_2173975 : Nat := 118140960795 + 2173975 * 2 ^ 59
def prefixEnd_2173975 : Nat := 4983230072969 + 3 ^ 40 * 2173975 * 2
def baseEnd_2173975 : Nat := 372098035286079015504859

theorem tailTrace_2173975 : CollatzResearch.WordTrace tailWord_2173975 prefixEnd_2173975 372098035286079015504859 := by
  unfold tailWord_2173975
  simp only [CollatzResearch.WordTrace]
  refine ⟨79291382299067335215571379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52860921532711556810380919 79291382299067335215571379)
  ·
    refine ⟨118937073448601002823357069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79291382299067335215571379 118937073448601002823357069)
    ·
      refine ⟨44601402543225376058758901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118937073448601002823357069 44601402543225376058758901)
      ·
        refine ⟨4181381488427379005508647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44601402543225376058758901 4181381488427379005508647)
        ·
          refine ⟨6272072232641068508262971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4181381488427379005508647 6272072232641068508262971)
          ·
            refine ⟨9408108348961602762394457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6272072232641068508262971 9408108348961602762394457)
            ·
              refine ⟨7056081261721202071795843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9408108348961602762394457 7056081261721202071795843)
              ·
                refine ⟨10584121892581803107693765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7056081261721202071795843 10584121892581803107693765)
                ·
                  refine ⟨1984522854859088082692581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10584121892581803107693765 1984522854859088082692581)
                  ·
                    refine ⟨372098035286079015504859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1984522854859088082692581 372098035286079015504859)
                    ·
                      rfl

theorem cell23_2173975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 4, 4].length) (baseStart_2173975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2173975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2173975 prefixEnd_2173975 := by exact prefixLift 2173975
  have htrace : WordTrace (prefixWord ++ tailWord_2173975) baseStart_2173975 baseEnd_2173975 := by
    simpa [prefixWord, tailWord_2173975, baseEnd_2173975] using wordTrace_append hprefix tailTrace_2173975
  have hstable : (prefixWord ++ tailWord_2173975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173975).length < 2 ^ (prefixWord ++ tailWord_2173975).sum := by decide
  have hdescent : baseEnd_2173975 < baseStart_2173975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173988 : List Nat := [2, 3, 1, 4, 1, 1, 1, 10]
def baseStart_2173988 : Nat := 118140960795 + 2173988 * 2 ^ 59
def prefixEnd_2173988 : Nat := 4983230072969 + 3 ^ 40 * 2173988 * 2
def baseEnd_2173988 : Nat := 41344473374323907246371

theorem tailTrace_2173988 : CollatzResearch.WordTrace tailWord_2173988 prefixEnd_2173988 41344473374323907246371 := by
  unfold tailWord_2173988
  simp only [CollatzResearch.WordTrace]
  refine ⟨39645928224010119217897309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52861237632013492290529745 39645928224010119217897309)
  ·
    refine ⟨14867223084003794706711491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39645928224010119217897309 14867223084003794706711491)
    ·
      refine ⟨22300834626005692060067237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14867223084003794706711491 22300834626005692060067237)
      ·
        refine ⟨4181406492376067261262607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22300834626005692060067237 4181406492376067261262607)
        ·
          refine ⟨6272109738564100891893911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4181406492376067261262607 6272109738564100891893911)
          ·
            refine ⟨9408164607846151337840867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6272109738564100891893911 9408164607846151337840867)
            ·
              refine ⟨14112246911769227006761301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9408164607846151337840867 14112246911769227006761301)
              ·
                refine ⟨41344473374323907246371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 14112246911769227006761301 41344473374323907246371)
                ·
                  rfl

theorem cell23_2173988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 10].length) (baseStart_2173988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2173988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2173988 prefixEnd_2173988 := by exact prefixLift 2173988
  have htrace : WordTrace (prefixWord ++ tailWord_2173988) baseStart_2173988 baseEnd_2173988 := by
    simpa [prefixWord, tailWord_2173988, baseEnd_2173988] using wordTrace_append hprefix tailTrace_2173988
  have hstable : (prefixWord ++ tailWord_2173988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173988).length < 2 ^ (prefixWord ++ tailWord_2173988).sum := by decide
  have hdescent : baseEnd_2173988 < baseStart_2173988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174048 : List Nat := [2, 1, 1, 3, 2, 2, 3, 1, 2, 6]
def baseStart_2174048 : Nat := 118140960795 + 2174048 * 2 ^ 59
def prefixEnd_2174048 : Nat := 4983230072969 + 3 ^ 40 * 2174048 * 2
def baseEnd_2174048 : Nat := 372110529982005086967247

theorem tailTrace_2174048 : CollatzResearch.WordTrace tailWord_2174048 prefixEnd_2174048 372110529982005086967247 := by
  unfold tailWord_2174048
  simp only [CollatzResearch.WordTrace]
  refine ⟨39647022413901434341489399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52862696551868579121985865 39647022413901434341489399)
  ·
    refine ⟨59470533620852151512234099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39647022413901434341489399 59470533620852151512234099)
    ·
      refine ⟨89205800431278227268351149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59470533620852151512234099 89205800431278227268351149)
      ·
        refine ⟨33452175161729335225631681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89205800431278227268351149 33452175161729335225631681)
        ·
          refine ⟨25089131371297001419223761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33452175161729335225631681 25089131371297001419223761)
          ·
            refine ⟨18816848528472751064417821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25089131371297001419223761 18816848528472751064417821)
            ·
              refine ⟨7056318198177281649156683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18816848528472751064417821 7056318198177281649156683)
              ·
                refine ⟨10584477297265922473735025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7056318198177281649156683 10584477297265922473735025)
                ·
                  refine ⟨7938357972949441855301269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10584477297265922473735025 7938357972949441855301269)
                  ·
                    refine ⟨372110529982005086967247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7938357972949441855301269 372110529982005086967247)
                    ·
                      rfl

theorem cell23_2174048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 2, 6].length) (baseStart_2174048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2174048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2174048 prefixEnd_2174048 := by exact prefixLift 2174048
  have htrace : WordTrace (prefixWord ++ tailWord_2174048) baseStart_2174048 baseEnd_2174048 := by
    simpa [prefixWord, tailWord_2174048, baseEnd_2174048] using wordTrace_append hprefix tailTrace_2174048
  have hstable : (prefixWord ++ tailWord_2174048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174048).length < 2 ^ (prefixWord ++ tailWord_2174048).sum := by decide
  have hdescent : baseEnd_2174048 < baseStart_2174048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174089 : List Nat := [1, 2, 1, 1, 4, 3, 3, 2, 2, 2, 2]
def baseStart_2174089 : Nat := 118140960795 + 2174089 * 2 ^ 59
def prefixEnd_2174089 : Nat := 4983230072969 + 3 ^ 40 * 2174089 * 2
def baseEnd_2174089 : Nat := 1116352642652849600489053

theorem tailTrace_2174089 : CollatzResearch.WordTrace tailWord_2174089 prefixEnd_2174089 1116352642652849600489053 := by
  unfold tailWord_2174089
  simp only [CollatzResearch.WordTrace]
  refine ⟨79295540220654332685221321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52863693480436221790147547 79295540220654332685221321)
  ·
    refine ⟨59471655165490749513915991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79295540220654332685221321 59471655165490749513915991)
    ·
      refine ⟨89207482748236124270873987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59471655165490749513915991 89207482748236124270873987)
      ·
        refine ⟨133811224122354186406310981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89207482748236124270873987 133811224122354186406310981)
        ·
          refine ⟨25089604522941409951183309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 133811224122354186406310981 25089604522941409951183309)
          ·
            refine ⟨9408601696103028731693741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25089604522941409951183309 9408601696103028731693741)
            ·
              refine ⟨3528225636038635774385153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9408601696103028731693741 3528225636038635774385153)
              ·
                refine ⟨2646169227028976830788865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3528225636038635774385153 2646169227028976830788865)
                ·
                  refine ⟨1984626920271732623091649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2646169227028976830788865 1984626920271732623091649)
                  ·
                    refine ⟨1488470190203799467318737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1984626920271732623091649 1488470190203799467318737)
                    ·
                      refine ⟨1116352642652849600489053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1488470190203799467318737 1116352642652849600489053)
                      ·
                        rfl

theorem cell23_2174089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 2, 2, 2, 2].length) (baseStart_2174089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2174089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2174089 prefixEnd_2174089 := by exact prefixLift 2174089
  have htrace : WordTrace (prefixWord ++ tailWord_2174089) baseStart_2174089 baseEnd_2174089 := by
    simpa [prefixWord, tailWord_2174089, baseEnd_2174089] using wordTrace_append hprefix tailTrace_2174089
  have hstable : (prefixWord ++ tailWord_2174089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174089).length < 2 ^ (prefixWord ++ tailWord_2174089).sum := by decide
  have hdescent : baseEnd_2174089 < baseStart_2174089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174115 : List Nat := [1, 1, 1, 4, 1, 1, 1, 4, 2, 5, 2]
def baseStart_2174115 : Nat := 118140960795 + 2174115 * 2 ^ 59
def prefixEnd_2174115 : Nat := 4983230072969 + 3 ^ 40 * 2174115 * 2
def baseEnd_2174115 : Nat := 1116365993149866498763933

theorem tailTrace_2174115 : CollatzResearch.WordTrace tailWord_2174115 prefixEnd_2174115 1116365993149866498763933 := by
  unfold tailWord_2174115
  simp only [CollatzResearch.WordTrace]
  refine ⟨79296488518560139125667799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52864325679040092750445199 79296488518560139125667799)
  ·
    refine ⟨118944732777840208688501699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79296488518560139125667799 118944732777840208688501699)
    ·
      refine ⟨178417099166760313032752549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118944732777840208688501699 178417099166760313032752549)
      ·
        refine ⟨33453206093767558693641103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 178417099166760313032752549 33453206093767558693641103)
        ·
          refine ⟨50179809140651338040461655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33453206093767558693641103 50179809140651338040461655)
          ·
            refine ⟨75269713710977007060692483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50179809140651338040461655 75269713710977007060692483)
            ·
              refine ⟨112904570566465510591038725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75269713710977007060692483 112904570566465510591038725)
              ·
                refine ⟨21169606981212283235819761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 112904570566465510591038725 21169606981212283235819761)
                ·
                  refine ⟨15877205235909212426864821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21169606981212283235819761 15877205235909212426864821)
                  ·
                    refine ⟨1488487990866488665018577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15877205235909212426864821 1488487990866488665018577)
                    ·
                      refine ⟨1116365993149866498763933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1488487990866488665018577 1116365993149866498763933)
                      ·
                        rfl

theorem cell23_2174115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 5, 2].length) (baseStart_2174115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2174115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2174115 prefixEnd_2174115 := by exact prefixLift 2174115
  have htrace : WordTrace (prefixWord ++ tailWord_2174115) baseStart_2174115 baseEnd_2174115 := by
    simpa [prefixWord, tailWord_2174115, baseEnd_2174115] using wordTrace_append hprefix tailTrace_2174115
  have hstable : (prefixWord ++ tailWord_2174115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174115).length < 2 ^ (prefixWord ++ tailWord_2174115).sum := by decide
  have hdescent : baseEnd_2174115 < baseStart_2174115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174129 : List Nat := [1, 2, 2, 5, 1, 3, 1, 3, 5]
def baseStart_2174129 : Nat := 118140960795 + 2174129 * 2 ^ 59
def prefixEnd_2174129 : Nat := 4983230072969 + 3 ^ 40 * 2174129 * 2
def baseEnd_2174129 : Nat := 124041464653225493776541

theorem tailTrace_2174129 : CollatzResearch.WordTrace tailWord_2174129 prefixEnd_2174129 124041464653225493776541 := by
  unfold tailWord_2174129
  simp only [CollatzResearch.WordTrace]
  refine ⟨79296999140509419516677441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52864666093672946344451627 79296999140509419516677441)
  ·
    refine ⟨59472749355382064637508081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79296999140509419516677441 59472749355382064637508081)
    ·
      refine ⟨44604562016536548478131061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59472749355382064637508081 44604562016536548478131061)
      ·
        refine ⟨4181677689050301419824787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44604562016536548478131061 4181677689050301419824787)
        ·
          refine ⟨6272516533575452129737181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4181677689050301419824787 6272516533575452129737181)
          ·
            refine ⟨2352193700090794548651443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6272516533575452129737181 2352193700090794548651443)
            ·
              refine ⟨3528290550136191822977165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2352193700090794548651443 3528290550136191822977165)
              ·
                refine ⟨1323108956301071933616437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3528290550136191822977165 1323108956301071933616437)
                ·
                  refine ⟨124041464653225493776541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1323108956301071933616437 124041464653225493776541)
                  ·
                    rfl

theorem cell23_2174129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 3, 5].length) (baseStart_2174129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2174129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2174129 prefixEnd_2174129 := by exact prefixLift 2174129
  have htrace : WordTrace (prefixWord ++ tailWord_2174129) baseStart_2174129 baseEnd_2174129 := by
    simpa [prefixWord, tailWord_2174129, baseEnd_2174129] using wordTrace_append hprefix tailTrace_2174129
  have hstable : (prefixWord ++ tailWord_2174129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174129).length < 2 ^ (prefixWord ++ tailWord_2174129).sum := by decide
  have hdescent : baseEnd_2174129 < baseStart_2174129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174142 : List Nat := [4, 2, 1, 1, 3, 2, 1, 2, 2, 5]
def baseStart_2174142 : Nat := 118140960795 + 2174142 * 2 ^ 59
def prefixEnd_2174142 : Nat := 4983230072969 + 3 ^ 40 * 2174142 * 2
def baseEnd_2174142 : Nat := 372126619042512631042103

theorem tailTrace_2174142 : CollatzResearch.WordTrace tailWord_2174142 prefixEnd_2174142 372126619042512631042103 := by
  unfold tailWord_2174142
  simp only [CollatzResearch.WordTrace]
  refine ⟨9912184161182790342112585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52864982192974881824600453 9912184161182790342112585)
  ·
    refine ⟨7434138120887092756584439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9912184161182790342112585 7434138120887092756584439)
    ·
      refine ⟨11151207181330639134876659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7434138120887092756584439 11151207181330639134876659)
      ·
        refine ⟨16726810771995958702314989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11151207181330639134876659 16726810771995958702314989)
        ·
          refine ⟨6272554039498484513368121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16726810771995958702314989 6272554039498484513368121)
          ·
            refine ⟨4704415529623863385026091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6272554039498484513368121 4704415529623863385026091)
            ·
              refine ⟨7056623294435795077539137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4704415529623863385026091 7056623294435795077539137)
              ·
                refine ⟨5292467470826846308154353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7056623294435795077539137 5292467470826846308154353)
                ·
                  refine ⟨3969350603120134731115765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5292467470826846308154353 3969350603120134731115765)
                  ·
                    refine ⟨372126619042512631042103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3969350603120134731115765 372126619042512631042103)
                    ·
                      rfl

theorem cell23_2174142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_2174142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2174142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2174142 prefixEnd_2174142 := by exact prefixLift 2174142
  have htrace : WordTrace (prefixWord ++ tailWord_2174142) baseStart_2174142 baseEnd_2174142 := by
    simpa [prefixWord, tailWord_2174142, baseEnd_2174142] using wordTrace_append hprefix tailTrace_2174142
  have hstable : (prefixWord ++ tailWord_2174142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174142).length < 2 ^ (prefixWord ++ tailWord_2174142).sum := by decide
  have hdescent : baseEnd_2174142 < baseStart_2174142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174146 : List Nat := [3, 5, 1, 1, 2, 2, 1, 1, 7]
def baseStart_2174146 : Nat := 118140960795 + 2174146 * 2 ^ 59
def prefixEnd_2174146 : Nat := 4983230072969 + 3 ^ 40 * 2174146 * 2
def baseEnd_2174146 : Nat := 124042434561128430830699

theorem tailTrace_2174146 : CollatzResearch.WordTrace tailWord_2174146 prefixEnd_2174146 124042434561128430830699 := by
  unfold tailWord_2174146
  simp only [CollatzResearch.WordTrace]
  refine ⟨19824404795361957855011573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52865079454298554280030861 19824404795361957855011573)
  ·
    refine ⟨1858537949565183548907335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19824404795361957855011573 1858537949565183548907335)
    ·
      refine ⟨2787806924347775323361003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1858537949565183548907335 2787806924347775323361003)
      ·
        refine ⟨4181710386521662985041505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2787806924347775323361003 4181710386521662985041505)
        ·
          refine ⟨3136282789891247238781129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4181710386521662985041505 3136282789891247238781129)
          ·
            refine ⟨2352212092418435429085847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3136282789891247238781129 2352212092418435429085847)
            ·
              refine ⟨3528318138627653143628771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2352212092418435429085847 3528318138627653143628771)
              ·
                refine ⟨5292477207941479715443157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3528318138627653143628771 5292477207941479715443157)
                ·
                  refine ⟨124042434561128430830699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5292477207941479715443157 124042434561128430830699)
                  ·
                    rfl

theorem cell23_2174146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_2174146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2174146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2174146 prefixEnd_2174146 := by exact prefixLift 2174146
  have htrace : WordTrace (prefixWord ++ tailWord_2174146) baseStart_2174146 baseEnd_2174146 := by
    simpa [prefixWord, tailWord_2174146, baseEnd_2174146] using wordTrace_append hprefix tailTrace_2174146
  have hstable : (prefixWord ++ tailWord_2174146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174146).length < 2 ^ (prefixWord ++ tailWord_2174146).sum := by decide
  have hdescent : baseEnd_2174146 < baseStart_2174146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174155 : List Nat := [1, 1, 1, 1, 3, 2, 2, 5, 3, 4]
def baseStart_2174155 : Nat := 118140960795 + 2174155 * 2 ^ 59
def prefixEnd_2174155 : Nat := 4983230072969 + 3 ^ 40 * 2174155 * 2
def baseEnd_2174155 : Nat := 372128844125348780754583

theorem tailTrace_2174155 : CollatzResearch.WordTrace tailWord_2174155 prefixEnd_2174155 372128844125348780754583 := by
  unfold tailWord_2174155
  simp only [CollatzResearch.WordTrace]
  refine ⟨79297947438415225957123919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52865298292276817304749279 79297947438415225957123919)
  ·
    refine ⟨118946921157622838935685879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79297947438415225957123919 118946921157622838935685879)
    ·
      refine ⟨178420381736434258403528819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118946921157622838935685879 178420381736434258403528819)
      ·
        refine ⟨267630572604651387605293229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178420381736434258403528819 267630572604651387605293229)
        ·
          refine ⟨100361464726744270351984961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 267630572604651387605293229 100361464726744270351984961)
          ·
            refine ⟨75271098545058202763988721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100361464726744270351984961 75271098545058202763988721)
            ·
              refine ⟨56453323908793652072991541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75271098545058202763988721 56453323908793652072991541)
              ·
                refine ⟨5292499116449404881842957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56453323908793652072991541 5292499116449404881842957)
                ·
                  refine ⟨1984687168668526830691109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5292499116449404881842957 1984687168668526830691109)
                  ·
                    refine ⟨372128844125348780754583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1984687168668526830691109 372128844125348780754583)
                    ·
                      rfl

theorem cell23_2174155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5, 3, 4].length) (baseStart_2174155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2174155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2174155 prefixEnd_2174155 := by exact prefixLift 2174155
  have htrace : WordTrace (prefixWord ++ tailWord_2174155) baseStart_2174155 baseEnd_2174155 := by
    simpa [prefixWord, tailWord_2174155, baseEnd_2174155] using wordTrace_append hprefix tailTrace_2174155
  have hstable : (prefixWord ++ tailWord_2174155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174155).length < 2 ^ (prefixWord ++ tailWord_2174155).sum := by decide
  have hdescent : baseEnd_2174155 < baseStart_2174155 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174157 : List Nat := [1, 6, 2, 2, 1, 2, 2, 1, 2, 2, 2]
def baseStart_2174157 : Nat := 118140960795 + 2174157 * 2 ^ 59
def prefixEnd_2174157 : Nat := 4983230072969 + 3 ^ 40 * 2174157 * 2
def baseEnd_2174157 : Nat := 1116387559337355334438741

theorem tailTrace_2174157 : CollatzResearch.WordTrace tailWord_2174157 prefixEnd_2174157 1116387559337355334438741 := by
  unfold tailWord_2174157
  simp only [CollatzResearch.WordTrace]
  refine ⟨79298020384407980298696725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52865346922938653532464483 79298020384407980298696725)
  ·
    refine ⟨3717094705519124076501409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 79298020384407980298696725 3717094705519124076501409)
    ·
      refine ⟨2787821029139343057376057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3717094705519124076501409 2787821029139343057376057)
      ·
        refine ⟨2090865771854507293032043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2787821029139343057376057 2090865771854507293032043)
        ·
          refine ⟨3136298657781760939548065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2090865771854507293032043 3136298657781760939548065)
          ·
            refine ⟨2352223993336320704661049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3136298657781760939548065 2352223993336320704661049)
            ·
              refine ⟨1764167995002240528495787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2352223993336320704661049 1764167995002240528495787)
              ·
                refine ⟨2646251992503360792743681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1764167995002240528495787 2646251992503360792743681)
                ·
                  refine ⟨1984688994377520594557761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2646251992503360792743681 1984688994377520594557761)
                  ·
                    refine ⟨1488516745783140445918321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1984688994377520594557761 1488516745783140445918321)
                    ·
                      refine ⟨1116387559337355334438741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1488516745783140445918321 1116387559337355334438741)
                      ·
                        rfl

theorem cell23_2174157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_2174157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2174157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2174157 prefixEnd_2174157 := by exact prefixLift 2174157
  have htrace : WordTrace (prefixWord ++ tailWord_2174157) baseStart_2174157 baseEnd_2174157 := by
    simpa [prefixWord, tailWord_2174157, baseEnd_2174157] using wordTrace_append hprefix tailTrace_2174157
  have hstable : (prefixWord ++ tailWord_2174157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174157).length < 2 ^ (prefixWord ++ tailWord_2174157).sum := by decide
  have hdescent : baseEnd_2174157 < baseStart_2174157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174162 : List Nat := [3, 2, 2, 2, 1, 1, 2, 1, 1, 6, 2]
def baseStart_2174162 : Nat := 118140960795 + 2174162 * 2 ^ 59
def prefixEnd_2174162 : Nat := 4983230072969 + 3 ^ 40 * 2174162 * 2
def baseEnd_2174162 : Nat := 1116390126740627814876217

theorem tailTrace_2174162 : CollatzResearch.WordTrace tailWord_2174162 prefixEnd_2174162 1116390126740627814876217 := by
  unfold tailWord_2174162
  simp only [CollatzResearch.WordTrace]
  refine ⟨19824550687347466538157185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52865468499593244101752493 19824550687347466538157185)
  ·
    refine ⟨14868413015510599903617889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19824550687347466538157185 14868413015510599903617889)
    ·
      refine ⟨11151309761632949927713417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14868413015510599903617889 11151309761632949927713417)
      ·
        refine ⟨8363482321224712445785063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11151309761632949927713417 8363482321224712445785063)
        ·
          refine ⟨12545223481837068668677595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8363482321224712445785063 12545223481837068668677595)
          ·
            refine ⟨18817835222755603003016393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12545223481837068668677595 18817835222755603003016393)
            ·
              refine ⟨14113376417066702252262295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18817835222755603003016393 14113376417066702252262295)
              ·
                refine ⟨21170064625600053378393443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14113376417066702252262295 21170064625600053378393443)
                ·
                  refine ⟨31755096938400080067590165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21170064625600053378393443 31755096938400080067590165)
                  ·
                    refine ⟨1488520168987503753168289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 31755096938400080067590165 1488520168987503753168289)
                    ·
                      refine ⟨1116390126740627814876217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1488520168987503753168289 1116390126740627814876217)
                      ·
                        rfl

theorem cell23_2174162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_2174162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2174162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2174162 prefixEnd_2174162 := by exact prefixLift 2174162
  have htrace : WordTrace (prefixWord ++ tailWord_2174162) baseStart_2174162 baseEnd_2174162 := by
    simpa [prefixWord, tailWord_2174162, baseEnd_2174162] using wordTrace_append hprefix tailTrace_2174162
  have hstable : (prefixWord ++ tailWord_2174162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174162).length < 2 ^ (prefixWord ++ tailWord_2174162).sum := by decide
  have hdescent : baseEnd_2174162 < baseStart_2174162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174206 : List Nat := [4, 2, 2, 1, 1, 3, 1, 4, 1, 4]
def baseStart_2174206 : Nat := 118140960795 + 2174206 * 2 ^ 59
def prefixEnd_2174206 : Nat := 4983230072969 + 3 ^ 40 * 2174206 * 2
def baseEnd_2174206 : Nat := 372137573296475214242005

theorem tailTrace_2174206 : CollatzResearch.WordTrace tailWord_2174206 prefixEnd_2174206 372137573296475214242005 := by
  unfold tailWord_2174206
  simp only [CollatzResearch.WordTrace]
  refine ⟨9912475945153807708403809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52866538374153641111486981 9912475945153807708403809)
  ·
    refine ⟨7434356958865355781302857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9912475945153807708403809 7434356958865355781302857)
    ·
      refine ⟨5575767719149016835977143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7434356958865355781302857 5575767719149016835977143)
      ·
        refine ⟨8363651578723525253965715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5575767719149016835977143 8363651578723525253965715)
        ·
          refine ⟨12545477368085287880948573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8363651578723525253965715 12545477368085287880948573)
          ·
            refine ⟨4704554013031982955355715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12545477368085287880948573 4704554013031982955355715)
            ·
              refine ⟨7056831019547974433033573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4704554013031982955355715 7056831019547974433033573)
              ·
                refine ⟨1323155816165245206193795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7056831019547974433033573 1323155816165245206193795)
                ·
                  refine ⟨1984733724247867809290693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1323155816165245206193795 1984733724247867809290693)
                  ·
                    refine ⟨372137573296475214242005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1984733724247867809290693 372137573296475214242005)
                    ·
                      rfl

theorem cell23_2174206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_2174206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2174206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2174206 prefixEnd_2174206 := by exact prefixLift 2174206
  have htrace : WordTrace (prefixWord ++ tailWord_2174206) baseStart_2174206 baseEnd_2174206 := by
    simpa [prefixWord, tailWord_2174206, baseEnd_2174206] using wordTrace_append hprefix tailTrace_2174206
  have hstable : (prefixWord ++ tailWord_2174206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174206).length < 2 ^ (prefixWord ++ tailWord_2174206).sum := by decide
  have hdescent : baseEnd_2174206 < baseStart_2174206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174239 : List Nat := [1, 1, 2, 4, 4, 1, 1, 1, 1, 5, 2]
def baseStart_2174239 : Nat := 118140960795 + 2174239 * 2 ^ 59
def prefixEnd_2174239 : Nat := 4983230072969 + 3 ^ 40 * 2174239 * 2
def baseEnd_2174239 : Nat := 1116429664751024013613363

theorem tailTrace_2174239 : CollatzResearch.WordTrace tailWord_2174239 prefixEnd_2174239 1116429664751024013613363 := by
  unfold tailWord_2174239
  simp only [CollatzResearch.WordTrace]
  refine ⟨79301011170110908303181771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52867340780073938868787847 79301011170110908303181771)
  ·
    refine ⟨118951516755166362454772657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79301011170110908303181771 118951516755166362454772657)
    ·
      refine ⟨89213637566374771841079493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118951516755166362454772657 89213637566374771841079493)
      ·
        refine ⟨16727557043695269720202405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89213637566374771841079493 16727557043695269720202405)
        ·
          refine ⟨3136416945692863072537951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16727557043695269720202405 3136416945692863072537951)
          ·
            refine ⟨4704625418539294608806927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3136416945692863072537951 4704625418539294608806927)
            ·
              refine ⟨7056938127808941913210391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4704625418539294608806927 7056938127808941913210391)
              ·
                refine ⟨10585407191713412869815587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7056938127808941913210391 10585407191713412869815587)
                ·
                  refine ⟨15878110787570119304723381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10585407191713412869815587 15878110787570119304723381)
                  ·
                    refine ⟨1488572886334698684817817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15878110787570119304723381 1488572886334698684817817)
                    ·
                      refine ⟨1116429664751024013613363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1488572886334698684817817 1116429664751024013613363)
                      ·
                        rfl

theorem cell23_2174239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 5, 2].length) (baseStart_2174239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2174239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2174239 prefixEnd_2174239 := by exact prefixLift 2174239
  have htrace : WordTrace (prefixWord ++ tailWord_2174239) baseStart_2174239 baseEnd_2174239 := by
    simpa [prefixWord, tailWord_2174239, baseEnd_2174239] using wordTrace_append hprefix tailTrace_2174239
  have hstable : (prefixWord ++ tailWord_2174239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174239).length < 2 ^ (prefixWord ++ tailWord_2174239).sum := by decide
  have hdescent : baseEnd_2174239 < baseStart_2174239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174255 : List Nat := [1, 1, 2, 1, 2, 1, 3, 5, 1, 1, 5]
def baseStart_2174255 : Nat := 118140960795 + 2174255 * 2 ^ 59
def prefixEnd_2174255 : Nat := 4983230072969 + 3 ^ 40 * 2174255 * 2
def baseEnd_2174255 : Nat := 1116437880441495951013289

theorem tailTrace_2174255 : CollatzResearch.WordTrace tailWord_2174255 prefixEnd_2174255 1116437880441495951013289 := by
  unfold tailWord_2174255
  simp only [CollatzResearch.WordTrace]
  refine ⟨79301594738052943035764219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52867729825368628690509479 79301594738052943035764219)
  ·
    refine ⟨118952392107079414553646329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79301594738052943035764219 118952392107079414553646329)
    ·
      refine ⟨89214294080309560915234747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118952392107079414553646329 89214294080309560915234747)
      ·
        refine ⟨133821441120464341372852121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89214294080309560915234747 133821441120464341372852121)
        ·
          refine ⟨100366080840348256029639091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133821441120464341372852121 100366080840348256029639091)
          ·
            refine ⟨150549121260522384044458637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100366080840348256029639091 150549121260522384044458637)
            ·
              refine ⟨56455920472695894016671989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 150549121260522384044458637 56455920472695894016671989)
              ·
                refine ⟨5292742544315240064062999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56455920472695894016671989 5292742544315240064062999)
                ·
                  refine ⟨7939113816472860096094499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5292742544315240064062999 7939113816472860096094499)
                  ·
                    refine ⟨11908670724709290144141749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7939113816472860096094499 11908670724709290144141749)
                    ·
                      refine ⟨1116437880441495951013289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11908670724709290144141749 1116437880441495951013289)
                      ·
                        rfl

theorem cell23_2174255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5, 1, 1, 5].length) (baseStart_2174255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2174255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2174255 prefixEnd_2174255 := by exact prefixLift 2174255
  have htrace : WordTrace (prefixWord ++ tailWord_2174255) baseStart_2174255 baseEnd_2174255 := by
    simpa [prefixWord, tailWord_2174255, baseEnd_2174255] using wordTrace_append hprefix tailTrace_2174255
  have hstable : (prefixWord ++ tailWord_2174255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174255).length < 2 ^ (prefixWord ++ tailWord_2174255).sum := by decide
  have hdescent : baseEnd_2174255 < baseStart_2174255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174289 : List Nat := [1, 2, 2, 1, 4, 1, 4, 2, 1, 2, 3]
def baseStart_2174289 : Nat := 118140960795 + 2174289 * 2 ^ 59
def prefixEnd_2174289 : Nat := 4983230072969 + 3 ^ 40 * 2174289 * 2
def baseEnd_2174289 : Nat := 1116455338783748817988133

theorem tailTrace_2174289 : CollatzResearch.WordTrace tailWord_2174289 prefixEnd_2174289 1116455338783748817988133 := by
  unfold tailWord_2174289
  simp only [CollatzResearch.WordTrace]
  refine ⟨79302834819929766842501921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52868556546619844561667947 79302834819929766842501921)
  ·
    refine ⟨59477126114947325131876441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79302834819929766842501921 59477126114947325131876441)
    ·
      refine ⟨44607844586210493848907331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59477126114947325131876441 44607844586210493848907331)
      ·
        refine ⟨66911766879315740773360997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44607844586210493848907331 66911766879315740773360997)
        ·
          refine ⟨12545956289871701395005187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66911766879315740773360997 12545956289871701395005187)
          ·
            refine ⟨18818934434807552092507781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12545956289871701395005187 18818934434807552092507781)
            ·
              refine ⟨3528550206526416017345209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18818934434807552092507781 3528550206526416017345209)
              ·
                refine ⟨2646412654894812013008907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3528550206526416017345209 2646412654894812013008907)
                ·
                  refine ⟨3969618982342218019513361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2646412654894812013008907 3969618982342218019513361)
                  ·
                    refine ⟨2977214236756663514635021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3969618982342218019513361 2977214236756663514635021)
                    ·
                      refine ⟨1116455338783748817988133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2977214236756663514635021 1116455338783748817988133)
                      ·
                        rfl

theorem cell23_2174289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 2, 1, 2, 3].length) (baseStart_2174289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2174289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2174289 prefixEnd_2174289 := by exact prefixLift 2174289
  have htrace : WordTrace (prefixWord ++ tailWord_2174289) baseStart_2174289 baseEnd_2174289 := by
    simpa [prefixWord, tailWord_2174289, baseEnd_2174289] using wordTrace_append hprefix tailTrace_2174289
  have hstable : (prefixWord ++ tailWord_2174289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174289).length < 2 ^ (prefixWord ++ tailWord_2174289).sum := by decide
  have hdescent : baseEnd_2174289 < baseStart_2174289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174319 : List Nat := [1, 1, 2, 1, 3, 1, 4, 4, 2, 1, 3]
def baseStart_2174319 : Nat := 118140960795 + 2174319 * 2 ^ 59
def prefixEnd_2174319 : Nat := 4983230072969 + 3 ^ 40 * 2174319 * 2
def baseEnd_2174319 : Nat := 1116470743203383700612995

theorem tailTrace_2174319 : CollatzResearch.WordTrace tailWord_2174319 prefixEnd_2174319 1116470743203383700612995 := by
  unfold tailWord_2174319
  simp only [CollatzResearch.WordTrace]
  refine ⟨79303929009821081966094011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52869286006547387977396007 79303929009821081966094011)
  ·
    refine ⟨118955893514731622949141017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79303929009821081966094011 118955893514731622949141017)
    ·
      refine ⟨89216920136048717211855763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118955893514731622949141017 89216920136048717211855763)
      ·
        refine ⟨133825380204073075817783645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89216920136048717211855763 133825380204073075817783645)
        ·
          refine ⟨50184517576527403431668867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133825380204073075817783645 50184517576527403431668867)
          ·
            refine ⟨75276776364791105147503301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50184517576527403431668867 75276776364791105147503301)
            ·
              refine ⟨14114395568398332215156869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75276776364791105147503301 14114395568398332215156869)
              ·
                refine ⟨2646449169074687290341913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14114395568398332215156869 2646449169074687290341913)
                ·
                  refine ⟨1984836876806015467756435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2646449169074687290341913 1984836876806015467756435)
                  ·
                    refine ⟨2977255315209023201634653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1984836876806015467756435 2977255315209023201634653)
                    ·
                      refine ⟨1116470743203383700612995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2977255315209023201634653 1116470743203383700612995)
                      ·
                        rfl

theorem cell23_2174319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 4, 2, 1, 3].length) (baseStart_2174319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2174319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2174319 prefixEnd_2174319 := by exact prefixLift 2174319
  have htrace : WordTrace (prefixWord ++ tailWord_2174319) baseStart_2174319 baseEnd_2174319 := by
    simpa [prefixWord, tailWord_2174319, baseEnd_2174319] using wordTrace_append hprefix tailTrace_2174319
  have hstable : (prefixWord ++ tailWord_2174319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174319).length < 2 ^ (prefixWord ++ tailWord_2174319).sum := by decide
  have hdescent : baseEnd_2174319 < baseStart_2174319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174362 : List Nat := [3, 1, 1, 4, 1, 1, 1, 3, 2, 1, 5]
def baseStart_2174362 : Nat := 118140960795 + 2174362 * 2 ^ 59
def prefixEnd_2174362 : Nat := 4983230072969 + 3 ^ 40 * 2174362 * 2
def baseEnd_2174362 : Nat := 1116492822871527032375297

theorem tailTrace_2174362 : CollatzResearch.WordTrace tailWord_2174362 prefixEnd_2174362 1116492822871527032375297 := by
  unfold tailWord_2174362
  simp only [CollatzResearch.WordTrace]
  refine ⟨19826374337166325077477335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52870331565776866873272893 19826374337166325077477335)
  ·
    refine ⟨29739561505749487616216003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19826374337166325077477335 29739561505749487616216003)
    ·
      refine ⟨44609342258624231424324005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29739561505749487616216003 44609342258624231424324005)
      ·
        refine ⟨8364251673492043392060751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44609342258624231424324005 8364251673492043392060751)
        ·
          refine ⟨12546377510238065088091127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8364251673492043392060751 12546377510238065088091127)
          ·
            refine ⟨18819566265357097632136691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12546377510238065088091127 18819566265357097632136691)
            ·
              refine ⟨28229349398035646448205037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18819566265357097632136691 28229349398035646448205037)
              ·
                refine ⟨10586006024263367418076889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28229349398035646448205037 10586006024263367418076889)
                ·
                  refine ⟨7939504518197525563557667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10586006024263367418076889 7939504518197525563557667)
                  ·
                    refine ⟨11909256777296288345336501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7939504518197525563557667 11909256777296288345336501)
                    ·
                      refine ⟨1116492822871527032375297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11909256777296288345336501 1116492822871527032375297)
                      ·
                        rfl

theorem cell23_2174362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_2174362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2174362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2174362 prefixEnd_2174362 := by exact prefixLift 2174362
  have htrace : WordTrace (prefixWord ++ tailWord_2174362) baseStart_2174362 baseEnd_2174362 := by
    simpa [prefixWord, tailWord_2174362, baseEnd_2174362] using wordTrace_append hprefix tailTrace_2174362
  have hstable : (prefixWord ++ tailWord_2174362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174362).length < 2 ^ (prefixWord ++ tailWord_2174362).sum := by decide
  have hdescent : baseEnd_2174362 < baseStart_2174362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174372 : List Nat := [2, 3, 1, 2, 1, 1, 1, 4, 2, 2, 4]
def baseStart_2174372 : Nat := 118140960795 + 2174372 * 2 ^ 59
def prefixEnd_2174372 : Nat := 4983230072969 + 3 ^ 40 * 2174372 * 2
def baseEnd_2174372 : Nat := 1116497957678071993250251

theorem tailTrace_2174372 : CollatzResearch.WordTrace tailWord_2174372 prefixEnd_2174372 1116497957678071993250251 := by
  unfold tailWord_2174372
  simp only [CollatzResearch.WordTrace]
  refine ⟨39652931039314536008886685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52870574719086048011848913 39652931039314536008886685)
  ·
    refine ⟨14869849139742951003332507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39652931039314536008886685 14869849139742951003332507)
    ·
      refine ⟨22304773709614426504998761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14869849139742951003332507 22304773709614426504998761)
      ·
        refine ⟨16728580282210819878749071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22304773709614426504998761 16728580282210819878749071)
        ·
          refine ⟨25092870423316229818123607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16728580282210819878749071 25092870423316229818123607)
          ·
            refine ⟨37639305634974344727185411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25092870423316229818123607 37639305634974344727185411)
            ·
              refine ⟨56458958452461517090778117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37639305634974344727185411 56458958452461517090778117)
              ·
                refine ⟨10586054709836534454520897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56458958452461517090778117 10586054709836534454520897)
                ·
                  refine ⟨7939541032377400840890673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10586054709836534454520897 7939541032377400840890673)
                  ·
                    refine ⟨5954655774283050630668005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7939541032377400840890673 5954655774283050630668005)
                    ·
                      refine ⟨1116497957678071993250251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5954655774283050630668005 1116497957678071993250251)
                      ·
                        rfl

theorem cell23_2174372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_2174372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2174372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2174372 prefixEnd_2174372 := by exact prefixLift 2174372
  have htrace : WordTrace (prefixWord ++ tailWord_2174372) baseStart_2174372 baseEnd_2174372 := by
    simpa [prefixWord, tailWord_2174372, baseEnd_2174372] using wordTrace_append hprefix tailTrace_2174372
  have hstable : (prefixWord ++ tailWord_2174372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174372).length < 2 ^ (prefixWord ++ tailWord_2174372).sum := by decide
  have hdescent : baseEnd_2174372 < baseStart_2174372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174389 : List Nat := [1, 3, 3, 2, 2, 2, 1, 1, 2, 2, 4]
def baseStart_2174389 : Nat := 118140960795 + 2174389 * 2 ^ 59
def prefixEnd_2174389 : Nat := 4983230072969 + 3 ^ 40 * 2174389 * 2
def baseEnd_2174389 : Nat := 1116506686849198426737673

theorem tailTrace_2174389 : CollatzResearch.WordTrace tailWord_2174389 prefixEnd_2174389 1116506686849198426737673 := by
  unfold tailWord_2174389
  simp only [CollatzResearch.WordTrace]
  refine ⟨79306482119567483921142221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52870988079711655947428147 79306482119567483921142221)
  ·
    refine ⟨29739930794837806470428333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79306482119567483921142221 29739930794837806470428333)
    ·
      refine ⟨11152474048064177426410625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29739930794837806470428333 11152474048064177426410625)
      ·
        refine ⟨8364355536048133069807969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11152474048064177426410625 8364355536048133069807969)
        ·
          refine ⟨6273266652036099802355977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8364355536048133069807969 6273266652036099802355977)
          ·
            refine ⟨4704949989027074851766983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6273266652036099802355977 4704949989027074851766983)
            ·
              refine ⟨7057424983540612277650475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4704949989027074851766983 7057424983540612277650475)
              ·
                refine ⟨10586137475310918416475713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7057424983540612277650475 10586137475310918416475713)
                ·
                  refine ⟨7939603106483188812356785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10586137475310918416475713 7939603106483188812356785)
                  ·
                    refine ⟨5954702329862391609267589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7939603106483188812356785 5954702329862391609267589)
                    ·
                      refine ⟨1116506686849198426737673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5954702329862391609267589 1116506686849198426737673)
                      ·
                        rfl

theorem cell23_2174389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_2174389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2174389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2174389 prefixEnd_2174389 := by exact prefixLift 2174389
  have htrace : WordTrace (prefixWord ++ tailWord_2174389) baseStart_2174389 baseEnd_2174389 := by
    simpa [prefixWord, tailWord_2174389, baseEnd_2174389] using wordTrace_append hprefix tailTrace_2174389
  have hstable : (prefixWord ++ tailWord_2174389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174389).length < 2 ^ (prefixWord ++ tailWord_2174389).sum := by decide
  have hdescent : baseEnd_2174389 < baseStart_2174389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174392 : List Nat := [2, 1, 2, 1, 2, 2, 3, 1, 1, 5, 3]
def baseStart_2174392 : Nat := 118140960795 + 2174392 * 2 ^ 59
def prefixEnd_2174392 : Nat := 4983230072969 + 3 ^ 40 * 2174392 * 2
def baseEnd_2174392 : Nat := 1116508227291161915000159

theorem tailTrace_2174392 : CollatzResearch.WordTrace tailWord_2174392 prefixEnd_2174392 1116508227291161915000159 := by
  unfold tailWord_2174392
  simp only [CollatzResearch.WordTrace]
  refine ⟨39653295769278307716750715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52871061025704410289000953 39653295769278307716750715)
  ·
    refine ⟨59479943653917461575126073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39653295769278307716750715 59479943653917461575126073)
    ·
      refine ⟨44609957740438096181344555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59479943653917461575126073 44609957740438096181344555)
      ·
        refine ⟨66914936610657144272016833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44609957740438096181344555 66914936610657144272016833)
        ·
          refine ⟨50186202457992858204012625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66914936610657144272016833 50186202457992858204012625)
          ·
            refine ⟨37639651843494643653009469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50186202457992858204012625 37639651843494643653009469)
            ·
              refine ⟨14114869441310491369878551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37639651843494643653009469 14114869441310491369878551)
              ·
                refine ⟨21172304161965737054817827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14114869441310491369878551 21172304161965737054817827)
                ·
                  refine ⟨31758456242948605582226741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21172304161965737054817827 31758456242948605582226741)
                  ·
                    refine ⟨2977355272776431773333757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31758456242948605582226741 2977355272776431773333757)
                    ·
                      refine ⟨1116508227291161915000159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2977355272776431773333757 1116508227291161915000159)
                      ·
                        rfl

theorem cell23_2174392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 1, 5, 3].length) (baseStart_2174392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2174392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2174392 prefixEnd_2174392 := by exact prefixLift 2174392
  have htrace : WordTrace (prefixWord ++ tailWord_2174392) baseStart_2174392 baseEnd_2174392 := by
    simpa [prefixWord, tailWord_2174392, baseEnd_2174392] using wordTrace_append hprefix tailTrace_2174392
  have hstable : (prefixWord ++ tailWord_2174392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174392).length < 2 ^ (prefixWord ++ tailWord_2174392).sum := by decide
  have hdescent : baseEnd_2174392 < baseStart_2174392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174466 : List Nat := [3, 4, 1, 2, 1, 1, 2, 1, 1, 3, 4]
def baseStart_2174466 : Nat := 118140960795 + 2174466 * 2 ^ 59
def prefixEnd_2174466 : Nat := 4983230072969 + 3 ^ 40 * 2174466 * 2
def baseEnd_2174466 : Nat := 1116546224859594625474819

theorem tailTrace_2174466 : CollatzResearch.WordTrace tailWord_2174466 prefixEnd_2174466 1116546224859594625474819 := by
  unfold tailWord_2174466
  simp only [CollatzResearch.WordTrace]
  refine ⟨19827322635072131517923813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52872860360192350714463501 19827322635072131517923813)
  ·
    refine ⟨3717622994076024659610715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19827322635072131517923813 3717622994076024659610715)
    ·
      refine ⟨5576434491114036989416073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3717622994076024659610715 5576434491114036989416073)
      ·
        refine ⟨4182325868335527742062055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5576434491114036989416073 4182325868335527742062055)
        ·
          refine ⟨6273488802503291613093083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4182325868335527742062055 6273488802503291613093083)
          ·
            refine ⟨9410233203754937419639625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6273488802503291613093083 9410233203754937419639625)
            ·
              refine ⟨7057674902816203064729719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9410233203754937419639625 7057674902816203064729719)
              ·
                refine ⟨10586512354224304597094579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7057674902816203064729719 10586512354224304597094579)
                ·
                  refine ⟨15879768531336456895641869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10586512354224304597094579 15879768531336456895641869)
                  ·
                    refine ⟨5954913199251171335865701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15879768531336456895641869 5954913199251171335865701)
                    ·
                      refine ⟨1116546224859594625474819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5954913199251171335865701 1116546224859594625474819)
                      ·
                        rfl

theorem cell23_2174466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_2174466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2174466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2174466 prefixEnd_2174466 := by exact prefixLift 2174466
  have htrace : WordTrace (prefixWord ++ tailWord_2174466) baseStart_2174466 baseEnd_2174466 := by
    simpa [prefixWord, tailWord_2174466, baseEnd_2174466] using wordTrace_append hprefix tailTrace_2174466
  have hstable : (prefixWord ++ tailWord_2174466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174466).length < 2 ^ (prefixWord ++ tailWord_2174466).sum := by decide
  have hdescent : baseEnd_2174466 < baseStart_2174466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174469 : List Nat := [1, 3, 1, 1, 2, 2, 1, 5, 2, 2, 3]
def baseStart_2174469 : Nat := 118140960795 + 2174469 * 2 ^ 59
def prefixEnd_2174469 : Nat := 4983230072969 + 3 ^ 40 * 2174469 * 2
def baseEnd_2174469 : Nat := 1116547765301558113737305

theorem tailTrace_2174469 : CollatzResearch.WordTrace tailWord_2174469 prefixEnd_2174469 1116547765301558113737305 := by
  unfold tailWord_2174469
  simp only [CollatzResearch.WordTrace]
  refine ⟨79309399959277657584054461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52872933306185105056036307 79309399959277657584054461)
  ·
    refine ⟨29741024984729121594020423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79309399959277657584054461 29741024984729121594020423)
    ·
      refine ⟨44611537477093682391030635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29741024984729121594020423 44611537477093682391030635)
      ·
        refine ⟨66917306215640523586545953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44611537477093682391030635 66917306215640523586545953)
        ·
          refine ⟨50187979661730392689909465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66917306215640523586545953 50187979661730392689909465)
          ·
            refine ⟨37640984746297794517432099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50187979661730392689909465 37640984746297794517432099)
            ·
              refine ⟨56461477119446691776148149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37640984746297794517432099 56461477119446691776148149)
              ·
                refine ⟨5293263479948127354013889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56461477119446691776148149 5293263479948127354013889)
                ·
                  refine ⟨3969947609961095515510417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5293263479948127354013889 3969947609961095515510417)
                  ·
                    refine ⟨2977460707470821636632813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3969947609961095515510417 2977460707470821636632813)
                    ·
                      refine ⟨1116547765301558113737305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2977460707470821636632813 1116547765301558113737305)
                      ·
                        rfl

theorem cell23_2174469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5, 2, 2, 3].length) (baseStart_2174469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2174469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2174469 prefixEnd_2174469 := by exact prefixLift 2174469
  have htrace : WordTrace (prefixWord ++ tailWord_2174469) baseStart_2174469 baseEnd_2174469 := by
    simpa [prefixWord, tailWord_2174469, baseEnd_2174469] using wordTrace_append hprefix tailTrace_2174469
  have hstable : (prefixWord ++ tailWord_2174469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174469).length < 2 ^ (prefixWord ++ tailWord_2174469).sum := by decide
  have hdescent : baseEnd_2174469 < baseStart_2174469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174472 : List Nat := [2, 1, 3, 2, 1, 1, 3, 2, 8]
def baseStart_2174472 : Nat := 118140960795 + 2174472 * 2 ^ 59
def prefixEnd_2174472 : Nat := 4983230072969 + 3 ^ 40 * 2174472 * 2
def baseEnd_2174472 : Nat := 124061033971502400222199

theorem tailTrace_2174472 : CollatzResearch.WordTrace tailWord_2174472 prefixEnd_2174472 124061033971502400222199 := by
  unfold tailWord_2174472
  simp only [CollatzResearch.WordTrace]
  refine ⟨39654754689133394548206835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52873006252177859397609113 39654754689133394548206835)
  ·
    refine ⟨59482132033700091822310253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39654754689133394548206835 59482132033700091822310253)
    ·
      refine ⟨22305799512637534433366345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59482132033700091822310253 22305799512637534433366345)
      ·
        refine ⟨16729349634478150825024759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22305799512637534433366345 16729349634478150825024759)
        ·
          refine ⟨25094024451717226237537139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16729349634478150825024759 25094024451717226237537139)
          ·
            refine ⟨37641036677575839356305709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25094024451717226237537139 37641036677575839356305709)
            ·
              refine ⟨14115388754090939758614641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37641036677575839356305709 14115388754090939758614641)
              ·
                refine ⟨10586541565568204818960981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14115388754090939758614641 10586541565568204818960981)
                ·
                  refine ⟨124061033971502400222199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10586541565568204818960981 124061033971502400222199)
                  ·
                    rfl

theorem cell23_2174472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 8].length) (baseStart_2174472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2174472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2174472 prefixEnd_2174472 := by exact prefixLift 2174472
  have htrace : WordTrace (prefixWord ++ tailWord_2174472) baseStart_2174472 baseEnd_2174472 := by
    simpa [prefixWord, tailWord_2174472, baseEnd_2174472] using wordTrace_append hprefix tailTrace_2174472
  have hstable : (prefixWord ++ tailWord_2174472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174472).length < 2 ^ (prefixWord ++ tailWord_2174472).sum := by decide
  have hdescent : baseEnd_2174472 < baseStart_2174472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174519 : List Nat := [1, 1, 3, 1, 2, 5, 1, 1, 3, 5]
def baseStart_2174519 : Nat := 118140960795 + 2174519 * 2 ^ 59
def prefixEnd_2174519 : Nat := 4983230072969 + 3 ^ 40 * 2174519 * 2
def baseEnd_2174519 : Nat := 372191146444760972704025

theorem tailTrace_2174519 : CollatzResearch.WordTrace tailWord_2174519 prefixEnd_2174519 372191146444760972704025 := by
  unfold tailWord_2174519
  simp only [CollatzResearch.WordTrace]
  refine ⟨79311223609096516123374611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52874149072731010748916407 79311223609096516123374611)
  ·
    refine ⟨118966835413644774185061917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79311223609096516123374611 118966835413644774185061917)
    ·
      refine ⟨44612563280116790319398219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118966835413644774185061917 44612563280116790319398219)
      ·
        refine ⟨66918844920175185479097329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44612563280116790319398219 66918844920175185479097329)
        ·
          refine ⟨50189133690131389109322997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66918844920175185479097329 50189133690131389109322997)
          ·
            refine ⟨4705231283449817728999031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50189133690131389109322997 4705231283449817728999031)
            ·
              refine ⟨7057846925174726593498547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4705231283449817728999031 7057846925174726593498547)
              ·
                refine ⟨10586770387762089890247821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7057846925174726593498547 10586770387762089890247821)
                ·
                  refine ⟨3970038895410783708842933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10586770387762089890247821 3970038895410783708842933)
                  ·
                    refine ⟨372191146444760972704025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3970038895410783708842933 372191146444760972704025)
                    ·
                      rfl

theorem cell23_2174519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 3, 5].length) (baseStart_2174519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2174519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2174519 prefixEnd_2174519 := by exact prefixLift 2174519
  have htrace : WordTrace (prefixWord ++ tailWord_2174519) baseStart_2174519 baseEnd_2174519 := by
    simpa [prefixWord, tailWord_2174519, baseEnd_2174519] using wordTrace_append hprefix tailTrace_2174519
  have hstable : (prefixWord ++ tailWord_2174519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174519).length < 2 ^ (prefixWord ++ tailWord_2174519).sum := by decide
  have hdescent : baseEnd_2174519 < baseStart_2174519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174533 : List Nat := [1, 3, 1, 1, 1, 4, 2, 5, 1, 1, 3]
def baseStart_2174533 : Nat := 118140960795 + 2174533 * 2 ^ 59
def prefixEnd_2174533 : Nat := 4983230072969 + 3 ^ 40 * 2174533 * 2
def baseEnd_2174533 : Nat := 1116580628063445863337011

theorem tailTrace_2174533 : CollatzResearch.WordTrace tailWord_2174533 prefixEnd_2174533 1116580628063445863337011 := by
  unfold tailWord_2174533
  simp only [CollatzResearch.WordTrace]
  refine ⟨79311734231045796514384253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52874489487363864342922835 79311734231045796514384253)
  ·
    refine ⟨29741900336642173692894095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79311734231045796514384253 29741900336642173692894095)
    ·
      refine ⟨44612850504963260539341143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29741900336642173692894095 44612850504963260539341143)
      ·
        refine ⟨66919275757444890809011715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44612850504963260539341143 66919275757444890809011715)
        ·
          refine ⟨100378913636167336213517573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66919275757444890809011715 100378913636167336213517573)
          ·
            refine ⟨18821046306781375540034545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100378913636167336213517573 18821046306781375540034545)
            ·
              refine ⟨14115784730086031655025909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18821046306781375540034545 14115784730086031655025909)
              ·
                refine ⟨1323354818445565467658679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14115784730086031655025909 1323354818445565467658679)
                ·
                  refine ⟨1985032227668348201488019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1323354818445565467658679 1985032227668348201488019)
                  ·
                    refine ⟨2977548341502522302232029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1985032227668348201488019 2977548341502522302232029)
                    ·
                      refine ⟨1116580628063445863337011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2977548341502522302232029 1116580628063445863337011)
                      ·
                        rfl

theorem cell23_2174533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 5, 1, 1, 3].length) (baseStart_2174533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2174533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2174533 prefixEnd_2174533 := by exact prefixLift 2174533
  have htrace : WordTrace (prefixWord ++ tailWord_2174533) baseStart_2174533 baseEnd_2174533 := by
    simpa [prefixWord, tailWord_2174533, baseEnd_2174533] using wordTrace_append hprefix tailTrace_2174533
  have hstable : (prefixWord ++ tailWord_2174533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174533).length < 2 ^ (prefixWord ++ tailWord_2174533).sum := by decide
  have hdescent : baseEnd_2174533 < baseStart_2174533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174556 : List Nat := [2, 2, 4, 1, 2, 1, 1, 2, 3, 1, 4]
def baseStart_2174556 : Nat := 118140960795 + 2174556 * 2 ^ 59
def prefixEnd_2174556 : Nat := 4983230072969 + 3 ^ 40 * 2174556 * 2
def baseEnd_2174556 : Nat := 1116592438118499273349405

theorem tailTrace_2174556 : CollatzResearch.WordTrace tailWord_2174556 prefixEnd_2174556 1116592438118499273349405 := by
  unfold tailWord_2174556
  simp only [CollatzResearch.WordTrace]
  refine ⟨39656286554981235721235761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52875048739974980961647681 39656286554981235721235761)
  ·
    refine ⟨29742214916235926790926821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39656286554981235721235761 29742214916235926790926821)
    ·
      refine ⟨5576665296794236273298779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29742214916235926790926821 5576665296794236273298779)
      ·
        refine ⟨8364997945191354409948169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5576665296794236273298779 8364997945191354409948169)
        ·
          refine ⟨6273748458893515807461127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8364997945191354409948169 6273748458893515807461127)
          ·
            refine ⟨9410622688340273711191691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6273748458893515807461127 9410622688340273711191691)
            ·
              refine ⟨14115934032510410566787537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9410622688340273711191691 14115934032510410566787537)
              ·
                refine ⟨10586950524382807925090653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14115934032510410566787537 10586950524382807925090653)
                ·
                  refine ⟨3970106446643552971908995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10586950524382807925090653 3970106446643552971908995)
                  ·
                    refine ⟨5955159669965329457863493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3970106446643552971908995 5955159669965329457863493)
                    ·
                      refine ⟨1116592438118499273349405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5955159669965329457863493 1116592438118499273349405)
                      ·
                        rfl

theorem cell23_2174556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_2174556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2174556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2174556 prefixEnd_2174556 := by exact prefixLift 2174556
  have htrace : WordTrace (prefixWord ++ tailWord_2174556) baseStart_2174556 baseEnd_2174556 := by
    simpa [prefixWord, tailWord_2174556, baseEnd_2174556] using wordTrace_append hprefix tailTrace_2174556
  have hstable : (prefixWord ++ tailWord_2174556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174556).length < 2 ^ (prefixWord ++ tailWord_2174556).sum := by decide
  have hdescent : baseEnd_2174556 < baseStart_2174556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174569 : List Nat := [1, 2, 1, 1, 1, 4, 3, 3, 1, 2, 4]
def baseStart_2174569 : Nat := 118140960795 + 2174569 * 2 ^ 59
def prefixEnd_2174569 : Nat := 4983230072969 + 3 ^ 40 * 2174569 * 2
def baseEnd_2174569 : Nat := 1116599113367007722486845

theorem tailTrace_2174569 : CollatzResearch.WordTrace tailWord_2174569 prefixEnd_2174569 1116599113367007722486845 := by
  unfold tailWord_2174569
  simp only [CollatzResearch.WordTrace]
  refine ⟨79313047258915374662694761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52875364839276916441796507 79313047258915374662694761)
  ·
    refine ⟨59484785444186530997021071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79313047258915374662694761 59484785444186530997021071)
    ·
      refine ⟨89227178166279796495531607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59484785444186530997021071 89227178166279796495531607)
      ·
        refine ⟨133840767249419694743297411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89227178166279796495531607 133840767249419694743297411)
        ·
          refine ⟨200761150874129542114946117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133840767249419694743297411 200761150874129542114946117)
          ·
            refine ⟨37642715788899289146552397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 200761150874129542114946117 37642715788899289146552397)
            ·
              refine ⟨14116018420837233429957149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37642715788899289146552397 14116018420837233429957149)
              ·
                refine ⟨5293506907813962536233931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14116018420837233429957149 5293506907813962536233931)
                ·
                  refine ⟨7940260361720943804350897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5293506907813962536233931 7940260361720943804350897)
                  ·
                    refine ⟨5955195271290707853263173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7940260361720943804350897 5955195271290707853263173)
                    ·
                      refine ⟨1116599113367007722486845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5955195271290707853263173 1116599113367007722486845)
                      ·
                        rfl

theorem cell23_2174569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3, 1, 2, 4].length) (baseStart_2174569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2174569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2174569 prefixEnd_2174569 := by exact prefixLift 2174569
  have htrace : WordTrace (prefixWord ++ tailWord_2174569) baseStart_2174569 baseEnd_2174569 := by
    simpa [prefixWord, tailWord_2174569, baseEnd_2174569] using wordTrace_append hprefix tailTrace_2174569
  have hstable : (prefixWord ++ tailWord_2174569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174569).length < 2 ^ (prefixWord ++ tailWord_2174569).sum := by decide
  have hdescent : baseEnd_2174569 < baseStart_2174569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174576 : List Nat := [2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 3]
def baseStart_2174576 : Nat := 118140960795 + 2174576 * 2 ^ 59
def prefixEnd_2174576 : Nat := 4983230072969 + 3 ^ 40 * 2174576 * 2
def baseEnd_2174576 : Nat := 1116602707731589195099313

theorem tailTrace_2174576 : CollatzResearch.WordTrace tailWord_2174576 prefixEnd_2174576 1116602707731589195099313 := by
  unfold tailWord_2174576
  simp only [CollatzResearch.WordTrace]
  refine ⟨39656651284945007429099791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52875535046593343238799721 39656651284945007429099791)
  ·
    refine ⟨59484976927417511143649687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39656651284945007429099791 59484976927417511143649687)
    ·
      refine ⟨89227465391126266715474531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59484976927417511143649687 89227465391126266715474531)
      ·
        refine ⟨133841198086689400073211797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89227465391126266715474531 133841198086689400073211797)
        ·
          refine ⟨6273806160313565628431803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 133841198086689400073211797 6273806160313565628431803)
          ·
            refine ⟨9410709240470348442647705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6273806160313565628431803 9410709240470348442647705)
            ·
              refine ⟨7058031930352761331985779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9410709240470348442647705 7058031930352761331985779)
              ·
                refine ⟨10587047895529141997978669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7058031930352761331985779 10587047895529141997978669)
                ·
                  refine ⟨3970142960823428249242001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10587047895529141997978669 3970142960823428249242001)
                  ·
                    refine ⟨2977607220617571186931501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3970142960823428249242001 2977607220617571186931501)
                    ·
                      refine ⟨1116602707731589195099313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2977607220617571186931501 1116602707731589195099313)
                      ·
                        rfl

theorem cell23_2174576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 3].length) (baseStart_2174576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2174576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2174576 prefixEnd_2174576 := by exact prefixLift 2174576
  have htrace : WordTrace (prefixWord ++ tailWord_2174576) baseStart_2174576 baseEnd_2174576 := by
    simpa [prefixWord, tailWord_2174576, baseEnd_2174576] using wordTrace_append hprefix tailTrace_2174576
  have hstable : (prefixWord ++ tailWord_2174576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174576).length < 2 ^ (prefixWord ++ tailWord_2174576).sum := by decide
  have hdescent : baseEnd_2174576 < baseStart_2174576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174593 : List Nat := [1, 2, 4, 2, 1, 3, 1, 3, 1, 2, 3]
def baseStart_2174593 : Nat := 118140960795 + 2174593 * 2 ^ 59
def prefixEnd_2174593 : Nat := 4983230072969 + 3 ^ 40 * 2174593 * 2
def baseEnd_2174593 : Nat := 1116611436902715628586735

theorem tailTrace_2174593 : CollatzResearch.WordTrace tailWord_2174593 prefixEnd_2174593 1116611436902715628586735 := by
  unfold tailWord_2174593
  simp only [CollatzResearch.WordTrace]
  refine ⟨79313922610828426761568433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52875948407218951174378955 79313922610828426761568433)
  ·
    refine ⟨59485441958121320071176325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79313922610828426761568433 59485441958121320071176325)
    ·
      refine ⟨11153520367147747513345561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59485441958121320071176325 11153520367147747513345561)
      ·
        refine ⟨8365140275360810635009171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11153520367147747513345561 8365140275360810635009171)
        ·
          refine ⟨12547710413041215952513757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8365140275360810635009171 12547710413041215952513757)
          ·
            refine ⟨4705391404890455982192659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12547710413041215952513757 4705391404890455982192659)
            ·
              refine ⟨7058087107335683973288989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4705391404890455982192659 7058087107335683973288989)
              ·
                refine ⟨2646782665250881489983371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7058087107335683973288989 2646782665250881489983371)
                ·
                  refine ⟨3970173997876322234975057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2646782665250881489983371 3970173997876322234975057)
                  ·
                    refine ⟨2977630498407241676231293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3970173997876322234975057 2977630498407241676231293)
                    ·
                      refine ⟨1116611436902715628586735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2977630498407241676231293 1116611436902715628586735)
                      ·
                        rfl

theorem cell23_2174593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_2174593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2174593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2174593 prefixEnd_2174593 := by exact prefixLift 2174593
  have htrace : WordTrace (prefixWord ++ tailWord_2174593) baseStart_2174593 baseEnd_2174593 := by
    simpa [prefixWord, tailWord_2174593, baseEnd_2174593] using wordTrace_append hprefix tailTrace_2174593
  have hstable : (prefixWord ++ tailWord_2174593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174593).length < 2 ^ (prefixWord ++ tailWord_2174593).sum := by decide
  have hdescent : baseEnd_2174593 < baseStart_2174593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174620 : List Nat := [2, 2, 3, 2, 4, 1, 1, 1, 1, 2, 4]
def baseStart_2174620 : Nat := 118140960795 + 2174620 * 2 ^ 59
def prefixEnd_2174620 : Nat := 4983230072969 + 3 ^ 40 * 2174620 * 2
def baseEnd_2174620 : Nat := 1116625300880387022949111

theorem tailTrace_2174620 : CollatzResearch.WordTrace tailWord_2174620 prefixEnd_2174620 1116625300880387022949111 := by
  unfold tailWord_2174620
  simp only [CollatzResearch.WordTrace]
  refine ⟨39657453690865305186400657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52876604921153740248534209 39657453690865305186400657)
  ·
    refine ⟨29743090268148978889800493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39657453690865305186400657 29743090268148978889800493)
    ·
      refine ⟨11153658850555867083675185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29743090268148978889800493 11153658850555867083675185)
      ·
        refine ⟨8365244137916900312756389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11153658850555867083675185 8365244137916900312756389)
        ·
          refine ⟨1568483275859418808641823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8365244137916900312756389 1568483275859418808641823)
          ·
            refine ⟨2352724913789128212962735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1568483275859418808641823 2352724913789128212962735)
            ·
              refine ⟨3529087370683692319444103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2352724913789128212962735 3529087370683692319444103)
              ·
                refine ⟨5293631056025538479166155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3529087370683692319444103 5293631056025538479166155)
                ·
                  refine ⟨7940446584038307718749233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5293631056025538479166155 7940446584038307718749233)
                  ·
                    refine ⟨5955334938028730789061925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7940446584038307718749233 5955334938028730789061925)
                    ·
                      refine ⟨1116625300880387022949111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5955334938028730789061925 1116625300880387022949111)
                      ·
                        rfl

theorem cell23_2174620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_2174620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2174620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2174620 prefixEnd_2174620 := by exact prefixLift 2174620
  have htrace : WordTrace (prefixWord ++ tailWord_2174620) baseStart_2174620 baseEnd_2174620 := by
    simpa [prefixWord, tailWord_2174620, baseEnd_2174620] using wordTrace_append hprefix tailTrace_2174620
  have hstable : (prefixWord ++ tailWord_2174620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174620).length < 2 ^ (prefixWord ++ tailWord_2174620).sum := by decide
  have hdescent : baseEnd_2174620 < baseStart_2174620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174629 : List Nat := [1, 3, 1, 2, 1, 2, 2, 2, 2, 3, 4]
def baseStart_2174629 : Nat := 118140960795 + 2174629 * 2 ^ 59
def prefixEnd_2174629 : Nat := 4983230072969 + 3 ^ 40 * 2174629 * 2
def baseEnd_2174629 : Nat := 1116629922206277487736569

theorem tailTrace_2174629 : CollatzResearch.WordTrace tailWord_2174629 prefixEnd_2174629 1116629922206277487736569 := by
  unfold tailWord_2174629
  simp only [CollatzResearch.WordTrace]
  refine ⟨79315235638698004909878941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52876823759132003273252627 79315235638698004909878941)
  ·
    refine ⟨29743213364511751841204603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79315235638698004909878941 29743213364511751841204603)
    ·
      refine ⟨44614820046767627761806905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29743213364511751841204603 44614820046767627761806905)
      ·
        refine ⟨33461115035075720821355179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44614820046767627761806905 33461115035075720821355179)
        ·
          refine ⟨50191672552613581232032769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33461115035075720821355179 50191672552613581232032769)
          ·
            refine ⟨37643754414460185924024577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50191672552613581232032769 37643754414460185924024577)
            ·
              refine ⟨28232815810845139443018433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37643754414460185924024577 28232815810845139443018433)
              ·
                refine ⟨21174611858133854582263825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28232815810845139443018433 21174611858133854582263825)
                ·
                  refine ⟨15880958893600390936697869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21174611858133854582263825 15880958893600390936697869)
                  ·
                    refine ⟨5955359585100146601261701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15880958893600390936697869 5955359585100146601261701)
                    ·
                      refine ⟨1116629922206277487736569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5955359585100146601261701 1116629922206277487736569)
                      ·
                        rfl

theorem cell23_2174629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_2174629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2174629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2174629 prefixEnd_2174629 := by exact prefixLift 2174629
  have htrace : WordTrace (prefixWord ++ tailWord_2174629) baseStart_2174629 baseEnd_2174629 := by
    simpa [prefixWord, tailWord_2174629, baseEnd_2174629] using wordTrace_append hprefix tailTrace_2174629
  have hstable : (prefixWord ++ tailWord_2174629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174629).length < 2 ^ (prefixWord ++ tailWord_2174629).sum := by decide
  have hdescent : baseEnd_2174629 < baseStart_2174629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174649 : List Nat := [1, 2, 1, 4, 1, 1, 3, 1, 1, 3, 5]
def baseStart_2174649 : Nat := 118140960795 + 2174649 * 2 ^ 59
def prefixEnd_2174649 : Nat := 4983230072969 + 3 ^ 40 * 2174649 * 2
def baseEnd_2174649 : Nat := 1116640191819367409486477

theorem tailTrace_2174649 : CollatzResearch.WordTrace tailWord_2174649 prefixEnd_2174649 1116640191819367409486477 := by
  unfold tailWord_2174649
  simp only [CollatzResearch.WordTrace]
  refine ⟨79315965098625548325607001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52877310065750365550404667 79315965098625548325607001)
  ·
    refine ⟨59486973823969161244205251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79315965098625548325607001 59486973823969161244205251)
    ·
      refine ⟨89230460735953741866307877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59486973823969161244205251 89230460735953741866307877)
      ·
        refine ⟨16730711387991326599932727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89230460735953741866307877 16730711387991326599932727)
        ·
          refine ⟨25096067081986989899899091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16730711387991326599932727 25096067081986989899899091)
          ·
            refine ⟨37644100622980484849848637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25096067081986989899899091 37644100622980484849848637)
            ·
              refine ⟨14116537733617681818693239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37644100622980484849848637 14116537733617681818693239)
              ·
                refine ⟨21174806600426522728039859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14116537733617681818693239 21174806600426522728039859)
                ·
                  refine ⟨31762209900639784092059789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21174806600426522728039859 31762209900639784092059789)
                  ·
                    refine ⟨11910828712739919034522421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31762209900639784092059789 11910828712739919034522421)
                    ·
                      refine ⟨1116640191819367409486477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11910828712739919034522421 1116640191819367409486477)
                      ·
                        rfl

theorem cell23_2174649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_2174649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2174649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2174649 prefixEnd_2174649 := by exact prefixLift 2174649
  have htrace : WordTrace (prefixWord ++ tailWord_2174649) baseStart_2174649 baseEnd_2174649 := by
    simpa [prefixWord, tailWord_2174649, baseEnd_2174649] using wordTrace_append hprefix tailTrace_2174649
  have hstable : (prefixWord ++ tailWord_2174649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174649).length < 2 ^ (prefixWord ++ tailWord_2174649).sum := by decide
  have hdescent : baseEnd_2174649 < baseStart_2174649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174658 : List Nat := [3, 5, 1, 2, 2, 1, 1, 1, 3, 2, 2]
def baseStart_2174658 : Nat := 118140960795 + 2174658 * 2 ^ 59
def prefixEnd_2174658 : Nat := 4983230072969 + 3 ^ 40 * 2174658 * 2
def baseEnd_2174658 : Nat := 1116644813145257874273937

theorem tailTrace_2174658 : CollatzResearch.WordTrace tailWord_2174658 prefixEnd_2174658 1116644813145257874273937 := by
  unfold tailWord_2174658
  simp only [CollatzResearch.WordTrace]
  refine ⟨19829073338898235715671157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52877528903728628575123085 19829073338898235715671157)
  ·
    refine ⟨1858975625521709598344171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19829073338898235715671157 1858975625521709598344171)
    ·
      refine ⟨2788463438282564397516257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1858975625521709598344171 2788463438282564397516257)
      ·
        refine ⟨2091347578711923298137193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2788463438282564397516257 2091347578711923298137193)
        ·
          refine ⟨1568510684033942473602895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2091347578711923298137193 1568510684033942473602895)
          ·
            refine ⟨2352766026050913710404343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1568510684033942473602895 2352766026050913710404343)
            ·
              refine ⟨3529149039076370565606515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2352766026050913710404343 3529149039076370565606515)
              ·
                refine ⟨5293723558614555848409773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3529149039076370565606515 5293723558614555848409773)
                ·
                  refine ⟨1985146334480458443153665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5293723558614555848409773 1985146334480458443153665)
                  ·
                    refine ⟨1488859750860343832365249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1985146334480458443153665 1488859750860343832365249)
                    ·
                      refine ⟨1116644813145257874273937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1488859750860343832365249 1116644813145257874273937)
                      ·
                        rfl

theorem cell23_2174658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_2174658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2174658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2174658 prefixEnd_2174658 := by exact prefixLift 2174658
  have htrace : WordTrace (prefixWord ++ tailWord_2174658) baseStart_2174658 baseEnd_2174658 := by
    simpa [prefixWord, tailWord_2174658, baseEnd_2174658] using wordTrace_append hprefix tailTrace_2174658
  have hstable : (prefixWord ++ tailWord_2174658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174658).length < 2 ^ (prefixWord ++ tailWord_2174658).sum := by decide
  have hdescent : baseEnd_2174658 < baseStart_2174658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174663 : List Nat := [1, 1, 4, 1, 1, 1, 3, 3, 4, 2, 2]
def baseStart_2174663 : Nat := 118140960795 + 2174663 * 2 ^ 59
def prefixEnd_2174663 : Nat := 4983230072969 + 3 ^ 40 * 2174663 * 2
def baseEnd_2174663 : Nat := 1116647380548530354711413

theorem tailTrace_2174663 : CollatzResearch.WordTrace tailWord_2174663 prefixEnd_2174663 1116647380548530354711413 := by
  unfold tailWord_2174663
  simp only [CollatzResearch.WordTrace]
  refine ⟨79316475720574828716616643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52877650480383219144411095 79316475720574828716616643)
  ·
    refine ⟨118974713580862243074924965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79316475720574828716616643 118974713580862243074924965)
    ·
      refine ⟨22307758796411670576548431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 118974713580862243074924965 22307758796411670576548431)
      ·
        refine ⟨33461638194617505864822647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22307758796411670576548431 33461638194617505864822647)
        ·
          refine ⟨50192457291926258797233971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33461638194617505864822647 50192457291926258797233971)
          ·
            refine ⟨75288685937889388195850957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50192457291926258797233971 75288685937889388195850957)
            ·
              refine ⟨28233257226708520573444109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75288685937889388195850957 28233257226708520573444109)
              ·
                refine ⟨10587471460015695215041541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28233257226708520573444109 10587471460015695215041541)
                ·
                  refine ⟨1985150898752942852820289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10587471460015695215041541 1985150898752942852820289)
                  ·
                    refine ⟨1488863174064707139615217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1985150898752942852820289 1488863174064707139615217)
                    ·
                      refine ⟨1116647380548530354711413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1488863174064707139615217 1116647380548530354711413)
                      ·
                        rfl

theorem cell23_2174663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 4, 2, 2].length) (baseStart_2174663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2174663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2174663 prefixEnd_2174663 := by exact prefixLift 2174663
  have htrace : WordTrace (prefixWord ++ tailWord_2174663) baseStart_2174663 baseEnd_2174663 := by
    simpa [prefixWord, tailWord_2174663, baseEnd_2174663] using wordTrace_append hprefix tailTrace_2174663
  have hstable : (prefixWord ++ tailWord_2174663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174663).length < 2 ^ (prefixWord ++ tailWord_2174663).sum := by decide
  have hdescent : baseEnd_2174663 < baseStart_2174663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174680 : List Nat := [2, 1, 2, 2, 3, 1, 3, 3, 2, 2, 2]
def baseStart_2174680 : Nat := 118140960795 + 2174680 * 2 ^ 59
def prefixEnd_2174680 : Nat := 4983230072969 + 3 ^ 40 * 2174680 * 2
def baseEnd_2174680 : Nat := 1116656109719656788198835

theorem tailTrace_2174680 : CollatzResearch.WordTrace tailWord_2174680 prefixEnd_2174680 1116656109719656788198835 := by
  unfold tailWord_2174680
  simp only [CollatzResearch.WordTrace]
  refine ⟨39658547880756620309992747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52878063841008827079990329 39658547880756620309992747)
  ·
    refine ⟨59487821821134930464989121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39658547880756620309992747 59487821821134930464989121)
    ·
      refine ⟨44615866365851197848741841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59487821821134930464989121 44615866365851197848741841)
      ·
        refine ⟨33461899774388398386556381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44615866365851197848741841 33461899774388398386556381)
        ·
          refine ⟨12548212415395649394958643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33461899774388398386556381 12548212415395649394958643)
          ·
            refine ⟨18822318623093474092437965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12548212415395649394958643 18822318623093474092437965)
            ·
              refine ⟨7058369483660052784664237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18822318623093474092437965 7058369483660052784664237)
              ·
                refine ⟨2646888556372519794249089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7058369483660052784664237 2646888556372519794249089)
                ·
                  refine ⟨1985166417279389845686817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2646888556372519794249089 1985166417279389845686817)
                  ·
                    refine ⟨1488874812959542384265113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1985166417279389845686817 1488874812959542384265113)
                    ·
                      refine ⟨1116656109719656788198835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1488874812959542384265113 1116656109719656788198835)
                      ·
                        rfl

theorem cell23_2174680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 3, 2, 2, 2].length) (baseStart_2174680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2174680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2174680 prefixEnd_2174680 := by exact prefixLift 2174680
  have htrace : WordTrace (prefixWord ++ tailWord_2174680) baseStart_2174680 baseEnd_2174680 := by
    simpa [prefixWord, tailWord_2174680, baseEnd_2174680] using wordTrace_append hprefix tailTrace_2174680
  have hstable : (prefixWord ++ tailWord_2174680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174680).length < 2 ^ (prefixWord ++ tailWord_2174680).sum := by decide
  have hdescent : baseEnd_2174680 < baseStart_2174680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174684 : List Nat := [2, 2, 5, 1, 2, 2, 1, 2, 1, 3, 2]
def baseStart_2174684 : Nat := 118140960795 + 2174684 * 2 ^ 59
def prefixEnd_2174684 : Nat := 4983230072969 + 3 ^ 40 * 2174684 * 2
def baseEnd_2174684 : Nat := 1116658163642274772548817

theorem tailTrace_2174684 : CollatzResearch.WordTrace tailWord_2174684 prefixEnd_2174684 1116658163642274772548817 := by
  unfold tailWord_2174684
  simp only [CollatzResearch.WordTrace]
  refine ⟨39658620826749374651565553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52878161102332499535420737 39658620826749374651565553)
  ·
    refine ⟨29743965620062030988674165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39658620826749374651565553 29743965620062030988674165)
    ·
      refine ⟨2788496776880815405188203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29743965620062030988674165 2788496776880815405188203)
      ·
        refine ⟨4182745165321223107782305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2788496776880815405188203 4182745165321223107782305)
        ·
          refine ⟨3137058873990917330836729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4182745165321223107782305 3137058873990917330836729)
          ·
            refine ⟨2352794155493187998127547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3137058873990917330836729 2352794155493187998127547)
            ·
              refine ⟨3529191233239781997191321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2352794155493187998127547 3529191233239781997191321)
              ·
                refine ⟨2646893424929836497893491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3529191233239781997191321 2646893424929836497893491)
                ·
                  refine ⟨3970340137394754746840237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2646893424929836497893491 3970340137394754746840237)
                  ·
                    refine ⟨1488877551523033030065089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3970340137394754746840237 1488877551523033030065089)
                    ·
                      refine ⟨1116658163642274772548817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1488877551523033030065089 1116658163642274772548817)
                      ·
                        rfl

theorem cell23_2174684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_2174684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2174684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2174684 prefixEnd_2174684 := by exact prefixLift 2174684
  have htrace : WordTrace (prefixWord ++ tailWord_2174684) baseStart_2174684 baseEnd_2174684 := by
    simpa [prefixWord, tailWord_2174684, baseEnd_2174684] using wordTrace_append hprefix tailTrace_2174684
  have hstable : (prefixWord ++ tailWord_2174684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174684).length < 2 ^ (prefixWord ++ tailWord_2174684).sum := by decide
  have hdescent : baseEnd_2174684 < baseStart_2174684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174699 : List Nat := [1, 1, 1, 1, 2, 4, 2, 3, 1, 7]
def baseStart_2174699 : Nat := 118140960795 + 2174699 * 2 ^ 59
def prefixEnd_2174699 : Nat := 4983230072969 + 3 ^ 40 * 2174699 * 2
def baseEnd_2174699 : Nat := 372221955284030737953749

theorem tailTrace_2174699 : CollatzResearch.WordTrace tailWord_2174699 prefixEnd_2174699 372221955284030737953749 := by
  unfold tailWord_2174699
  simp only [CollatzResearch.WordTrace]
  refine ⟨79317788748444406864927151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52878525832296271243284767 79317788748444406864927151)
  ·
    refine ⟨118976683122666610297390727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79317788748444406864927151 118976683122666610297390727)
    ·
      refine ⟨178465024683999915446086091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118976683122666610297390727 178465024683999915446086091)
      ·
        refine ⟨267697537025999873169129137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178465024683999915446086091 267697537025999873169129137)
        ·
          refine ⟨200773152769499904876846853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 267697537025999873169129137 200773152769499904876846853)
          ·
            refine ⟨37644966144281232164408785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 200773152769499904876846853 37644966144281232164408785)
            ·
              refine ⟨28233724608210924123306589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37644966144281232164408785 28233724608210924123306589)
              ·
                refine ⟨10587646728079096546239971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28233724608210924123306589 10587646728079096546239971)
                ·
                  refine ⟨15881470092118644819359957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10587646728079096546239971 15881470092118644819359957)
                  ·
                    refine ⟨372221955284030737953749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15881470092118644819359957 372221955284030737953749)
                    ·
                      rfl

theorem cell23_2174699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 7].length) (baseStart_2174699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2174699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2174699 prefixEnd_2174699 := by exact prefixLift 2174699
  have htrace : WordTrace (prefixWord ++ tailWord_2174699) baseStart_2174699 baseEnd_2174699 := by
    simpa [prefixWord, tailWord_2174699, baseEnd_2174699] using wordTrace_append hprefix tailTrace_2174699
  have hstable : (prefixWord ++ tailWord_2174699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174699).length < 2 ^ (prefixWord ++ tailWord_2174699).sum := by decide
  have hdescent : baseEnd_2174699 < baseStart_2174699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174716 : List Nat := [2, 2, 2, 1, 3, 1, 1, 4, 2, 5]
def baseStart_2174716 : Nat := 118140960795 + 2174716 * 2 ^ 59
def prefixEnd_2174716 : Nat := 4983230072969 + 3 ^ 40 * 2174716 * 2
def baseEnd_2174716 : Nat := 372224865007739549116223

theorem tailTrace_2174716 : CollatzResearch.WordTrace tailWord_2174716 prefixEnd_2174716 372224865007739549116223 := by
  unfold tailWord_2174716
  simp only [CollatzResearch.WordTrace]
  refine ⟨39659204394691409384148001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52878939192921879178864001 39659204394691409384148001)
  ·
    refine ⟨29744403296018557038111001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39659204394691409384148001 29744403296018557038111001)
    ·
      refine ⟨22308302472013917778583251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29744403296018557038111001 22308302472013917778583251)
      ·
        refine ⟨33462453708020876667874877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22308302472013917778583251 33462453708020876667874877)
        ·
          refine ⟨12548420140507828750453079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33462453708020876667874877 12548420140507828750453079)
          ·
            refine ⟨18822630210761743125679619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12548420140507828750453079 18822630210761743125679619)
            ·
              refine ⟨28233945316142614688519429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18822630210761743125679619 28233945316142614688519429)
              ·
                refine ⟨5293864746776740254097393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28233945316142614688519429 5293864746776740254097393)
                ·
                  refine ⟨3970398560082555190573045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5293864746776740254097393 3970398560082555190573045)
                  ·
                    refine ⟨372224865007739549116223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3970398560082555190573045 372224865007739549116223)
                    ·
                      rfl

theorem cell23_2174716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4, 2, 5].length) (baseStart_2174716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2174716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2174716 prefixEnd_2174716 := by exact prefixLift 2174716
  have htrace : WordTrace (prefixWord ++ tailWord_2174716) baseStart_2174716 baseEnd_2174716 := by
    simpa [prefixWord, tailWord_2174716, baseEnd_2174716] using wordTrace_append hprefix tailTrace_2174716
  have hstable : (prefixWord ++ tailWord_2174716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174716).length < 2 ^ (prefixWord ++ tailWord_2174716).sum := by decide
  have hdescent : baseEnd_2174716 < baseStart_2174716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174729 : List Nat := [1, 2, 1, 1, 3, 2, 1, 2, 2, 8]
def baseStart_2174729 : Nat := 118140960795 + 2174729 * 2 ^ 59
def prefixEnd_2174729 : Nat := 4983230072969 + 3 ^ 40 * 2174729 * 2
def baseEnd_2174729 : Nat := 372227090090575698828703

theorem tailTrace_2174729 : CollatzResearch.WordTrace tailWord_2174729 prefixEnd_2174729 372227090090575698828703 := by
  unfold tailWord_2174729
  simp only [CollatzResearch.WordTrace]
  refine ⟨79318882938335721988519241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52879255292223814659012827 79318882938335721988519241)
  ·
    refine ⟨59489162203751791491389431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79318882938335721988519241 59489162203751791491389431)
    ·
      refine ⟨89233743305627687237084147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59489162203751791491389431 89233743305627687237084147)
      ·
        refine ⟨133850614958441530855626221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89233743305627687237084147 133850614958441530855626221)
        ·
          refine ⟨50193980609415574070859833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133850614958441530855626221 50193980609415574070859833)
          ·
            refine ⟨37645485457061680553144875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50193980609415574070859833 37645485457061680553144875)
            ·
              refine ⟨56468228185592520829717313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37645485457061680553144875 56468228185592520829717313)
              ·
                refine ⟨42351171139194390622287985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56468228185592520829717313 42351171139194390622287985)
                ·
                  refine ⟨31763378354395792966715989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42351171139194390622287985 31763378354395792966715989)
                  ·
                    refine ⟨372227090090575698828703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 31763378354395792966715989 372227090090575698828703)
                    ·
                      rfl

theorem cell23_2174729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 8].length) (baseStart_2174729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2174729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2174729 prefixEnd_2174729 := by exact prefixLift 2174729
  have htrace : WordTrace (prefixWord ++ tailWord_2174729) baseStart_2174729 baseEnd_2174729 := by
    simpa [prefixWord, tailWord_2174729, baseEnd_2174729] using wordTrace_append hprefix tailTrace_2174729
  have hstable : (prefixWord ++ tailWord_2174729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174729).length < 2 ^ (prefixWord ++ tailWord_2174729).sum := by decide
  have hdescent : baseEnd_2174729 < baseStart_2174729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174753 : List Nat := [1, 2, 3, 2, 1, 3, 3, 1, 2, 1, 4]
def baseStart_2174753 : Nat := 118140960795 + 2174753 * 2 ^ 59
def prefixEnd_2174753 : Nat := 4983230072969 + 3 ^ 40 * 2174753 * 2
def baseEnd_2174753 : Nat := 1116693593807435002585999

theorem tailTrace_2174753 : CollatzResearch.WordTrace tailWord_2174753 prefixEnd_2174753 1116693593807435002585999 := by
  unfold tailWord_2174753
  simp only [CollatzResearch.WordTrace]
  refine ⟨79319758290248774087392913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52879838860165849391595275 79319758290248774087392913)
  ·
    refine ⟨59489818717686580565544685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79319758290248774087392913 59489818717686580565544685)
    ·
      refine ⟨22308682019132467712079257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59489818717686580565544685 22308682019132467712079257)
      ·
        refine ⟨16731511514349350784059443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22308682019132467712079257 16731511514349350784059443)
        ·
          refine ⟨25097267271524026176089165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16731511514349350784059443 25097267271524026176089165)
          ·
            refine ⟨9411475226821509816033437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25097267271524026176089165 9411475226821509816033437)
            ·
              refine ⟨3529303210058066181012539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9411475226821509816033437 3529303210058066181012539)
              ·
                refine ⟨5293954815087099271518809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3529303210058066181012539 5293954815087099271518809)
                ·
                  refine ⟨3970466111315324453639107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5293954815087099271518809 3970466111315324453639107)
                  ·
                    refine ⟨5955699166972986680458661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3970466111315324453639107 5955699166972986680458661)
                    ·
                      refine ⟨1116693593807435002585999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5955699166972986680458661 1116693593807435002585999)
                      ·
                        rfl

theorem cell23_2174753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_2174753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2174753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2174753 prefixEnd_2174753 := by exact prefixLift 2174753
  have htrace : WordTrace (prefixWord ++ tailWord_2174753) baseStart_2174753 baseEnd_2174753 := by
    simpa [prefixWord, tailWord_2174753, baseEnd_2174753] using wordTrace_append hprefix tailTrace_2174753
  have hstable : (prefixWord ++ tailWord_2174753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174753).length < 2 ^ (prefixWord ++ tailWord_2174753).sum := by decide
  have hdescent : baseEnd_2174753 < baseStart_2174753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174776 : List Nat := [2, 1, 2, 1, 3, 4, 1, 1, 8]
def baseStart_2174776 : Nat := 118140960795 + 2174776 * 2 ^ 59
def prefixEnd_2174776 : Nat := 4983230072969 + 3 ^ 40 * 2174776 * 2
def baseEnd_2174776 : Nat := 124078378206943156955377

theorem tailTrace_2174776 : CollatzResearch.WordTrace tailWord_2174776 prefixEnd_2174776 124078378206943156955377 := by
  unfold tailWord_2174776
  simp only [CollatzResearch.WordTrace]
  refine ⟨39660298584582724507740091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52880398112776966010320121 39660298584582724507740091)
  ·
    refine ⟨59490447876874086761610137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39660298584582724507740091 59490447876874086761610137)
    ·
      refine ⟨44617835907655565071207603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59490447876874086761610137 44617835907655565071207603)
      ·
        refine ⟨66926753861483347606811405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44617835907655565071207603 66926753861483347606811405)
        ·
          refine ⟨25097532698056255352554277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66926753861483347606811405 25097532698056255352554277)
          ·
            refine ⟨4705787380885547878603927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25097532698056255352554277 4705787380885547878603927)
            ·
              refine ⟨7058681071328321817905891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4705787380885547878603927 7058681071328321817905891)
              ·
                refine ⟨10588021606992482726858837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7058681071328321817905891 10588021606992482726858837)
                ·
                  refine ⟨124078378206943156955377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10588021606992482726858837 124078378206943156955377)
                  ·
                    rfl

theorem cell23_2174776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 8].length) (baseStart_2174776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2174776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2174776 prefixEnd_2174776 := by exact prefixLift 2174776
  have htrace : WordTrace (prefixWord ++ tailWord_2174776) baseStart_2174776 baseEnd_2174776 := by
    simpa [prefixWord, tailWord_2174776, baseEnd_2174776] using wordTrace_append hprefix tailTrace_2174776
  have hstable : (prefixWord ++ tailWord_2174776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174776).length < 2 ^ (prefixWord ++ tailWord_2174776).sum := by decide
  have hdescent : baseEnd_2174776 < baseStart_2174776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174780 : List Nat := [2, 2, 2, 2, 1, 1, 4, 4, 1, 4]
def baseStart_2174780 : Nat := 118140960795 + 2174780 * 2 ^ 59
def prefixEnd_2174780 : Nat := 4983230072969 + 3 ^ 40 * 2174780 * 2
def baseEnd_2174780 : Nat := 372235819261702132316125

theorem tailTrace_2174780 : CollatzResearch.WordTrace tailWord_2174780 prefixEnd_2174780 372235819261702132316125 := by
  unfold tailWord_2174780
  simp only [CollatzResearch.WordTrace]
  refine ⟨39660371530575478849312897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52880495374100638465750529 39660371530575478849312897)
  ·
    refine ⟨29745278647931609136984673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39660371530575478849312897 29745278647931609136984673)
    ·
      refine ⟨22308958985948706852738505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29745278647931609136984673 22308958985948706852738505)
      ·
        refine ⟨16731719239461530139553879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22308958985948706852738505 16731719239461530139553879)
        ·
          refine ⟨25097578859192295209330819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16731719239461530139553879 25097578859192295209330819)
          ·
            refine ⟨37646368288788442813996229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25097578859192295209330819 37646368288788442813996229)
            ·
              refine ⟨7058694054147833027624293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37646368288788442813996229 7058694054147833027624293)
              ·
                refine ⟨1323505135152718692679555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7058694054147833027624293 1323505135152718692679555)
                ·
                  refine ⟨1985257702729078039019333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1323505135152718692679555 1985257702729078039019333)
                  ·
                    refine ⟨372235819261702132316125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1985257702729078039019333 372235819261702132316125)
                    ·
                      rfl

theorem cell23_2174780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 4, 1, 4].length) (baseStart_2174780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2174780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2174780 prefixEnd_2174780 := by exact prefixLift 2174780
  have htrace : WordTrace (prefixWord ++ tailWord_2174780) baseStart_2174780 baseEnd_2174780 := by
    simpa [prefixWord, tailWord_2174780, baseEnd_2174780] using wordTrace_append hprefix tailTrace_2174780
  have hstable : (prefixWord ++ tailWord_2174780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174780).length < 2 ^ (prefixWord ++ tailWord_2174780).sum := by decide
  have hdescent : baseEnd_2174780 < baseStart_2174780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174793 : List Nat := [1, 2, 1, 1, 2, 4, 5, 1, 6]
def baseStart_2174793 : Nat := 118140960795 + 2174793 * 2 ^ 59
def prefixEnd_2174793 : Nat := 4983230072969 + 3 ^ 40 * 2174793 * 2
def baseEnd_2174793 : Nat := 124079348114846094009535

theorem tailTrace_2174793 : CollatzResearch.WordTrace tailWord_2174793 prefixEnd_2174793 124079348114846094009535 := by
  unfold tailWord_2174793
  simp only [CollatzResearch.WordTrace]
  refine ⟨79321217210103860918849033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52880811473402573945899355 79321217210103860918849033)
  ·
    refine ⟨59490912907577895689136775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79321217210103860918849033 59490912907577895689136775)
    ·
      refine ⟨89236369361366843533705163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59490912907577895689136775 89236369361366843533705163)
      ·
        refine ⟨133854554042050265300557745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89236369361366843533705163 133854554042050265300557745)
        ·
          refine ⟨100390915531537698975418309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133854554042050265300557745 100390915531537698975418309)
          ·
            refine ⟨18823296662163318557890933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100390915531537698975418309 18823296662163318557890933)
            ·
              refine ⟨1764684062077811114802275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18823296662163318557890933 1764684062077811114802275)
              ·
                refine ⟨2647026093116716672203413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1764684062077811114802275 2647026093116716672203413)
                ·
                  refine ⟨124079348114846094009535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2647026093116716672203413 124079348114846094009535)
                  ·
                    rfl

theorem cell23_2174793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 1, 6].length) (baseStart_2174793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2174793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2174793 prefixEnd_2174793 := by exact prefixLift 2174793
  have htrace : WordTrace (prefixWord ++ tailWord_2174793) baseStart_2174793 baseEnd_2174793 := by
    simpa [prefixWord, tailWord_2174793, baseEnd_2174793] using wordTrace_append hprefix tailTrace_2174793
  have hstable : (prefixWord ++ tailWord_2174793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174793).length < 2 ^ (prefixWord ++ tailWord_2174793).sum := by decide
  have hdescent : baseEnd_2174793 < baseStart_2174793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174823 : List Nat := [1, 1, 5, 1, 2, 1, 1, 5, 1, 5]
def baseStart_2174823 : Nat := 118140960795 + 2174823 * 2 ^ 59
def prefixEnd_2174823 : Nat := 4983230072969 + 3 ^ 40 * 2174823 * 2
def baseEnd_2174823 : Nat := 372243179151083242903559

theorem tailTrace_2174823 : CollatzResearch.WordTrace tailWord_2174823 prefixEnd_2174823 372243179151083242903559 := by
  unfold tailWord_2174823
  simp only [CollatzResearch.WordTrace]
  refine ⟨79322311399995176042441123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52881540933330117361627415 79322311399995176042441123)
  ·
    refine ⟨118983467099992764063661685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79322311399995176042441123 118983467099992764063661685)
    ·
      refine ⟨11154700040624321630968283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 118983467099992764063661685 11154700040624321630968283)
      ·
        refine ⟨16732050060936482446452425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11154700040624321630968283 16732050060936482446452425)
        ·
          refine ⟨12549037545702361834839319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16732050060936482446452425 12549037545702361834839319)
          ·
            refine ⟨18823556318553542752258979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12549037545702361834839319 18823556318553542752258979)
            ·
              refine ⟨28235334477830314128388469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18823556318553542752258979 28235334477830314128388469)
              ·
                refine ⟨2647062607296591949536419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28235334477830314128388469 2647062607296591949536419)
                ·
                  refine ⟨3970593910944887924304629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2647062607296591949536419 3970593910944887924304629)
                  ·
                    refine ⟨372243179151083242903559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3970593910944887924304629 372243179151083242903559)
                    ·
                      rfl

theorem cell23_2174823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_2174823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2174823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2174823 prefixEnd_2174823 := by exact prefixLift 2174823
  have htrace : WordTrace (prefixWord ++ tailWord_2174823) baseStart_2174823 baseEnd_2174823 := by
    simpa [prefixWord, tailWord_2174823, baseEnd_2174823] using wordTrace_append hprefix tailTrace_2174823
  have hstable : (prefixWord ++ tailWord_2174823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174823).length < 2 ^ (prefixWord ++ tailWord_2174823).sum := by decide
  have hdescent : baseEnd_2174823 < baseStart_2174823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174860 : List Nat := [2, 2, 1, 2, 1, 2, 1, 3, 5, 2, 2]
def baseStart_2174860 : Nat := 118140960795 + 2174860 * 2 ^ 59
def prefixEnd_2174860 : Nat := 4983230072969 + 3 ^ 40 * 2174860 * 2
def baseEnd_2174860 : Nat := 1116748536237466083948007

theorem tailTrace_2174860 : CollatzResearch.WordTrace tailWord_2174860 prefixEnd_2174860 1116748536237466083948007 := by
  unfold tailWord_2174860
  simp only [CollatzResearch.WordTrace]
  refine ⟨39661830450430565680769017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52882440600574087574358689 39661830450430565680769017)
  ·
    refine ⟨29746372837822924260576763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39661830450430565680769017 29746372837822924260576763)
    ·
      refine ⟨44619559256734386390865145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29746372837822924260576763 44619559256734386390865145)
      ·
        refine ⟨33464669442550789793148859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44619559256734386390865145 33464669442550789793148859)
        ·
          refine ⟨50197004163826184689723289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33464669442550789793148859 50197004163826184689723289)
          ·
            refine ⟨37647753122869638517292467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50197004163826184689723289 37647753122869638517292467)
            ·
              refine ⟨56471629684304457775938701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37647753122869638517292467 56471629684304457775938701)
              ·
                refine ⟨21176861131614171665977013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56471629684304457775938701 21176861131614171665977013)
                ·
                  refine ⟨1985330731088828593685345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21176861131614171665977013 1985330731088828593685345)
                  ·
                    refine ⟨1488998048316621445264009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1985330731088828593685345 1488998048316621445264009)
                    ·
                      refine ⟨1116748536237466083948007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1488998048316621445264009 1116748536237466083948007)
                      ·
                        rfl

theorem cell23_2174860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 5, 2, 2].length) (baseStart_2174860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2174860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2174860 prefixEnd_2174860 := by exact prefixLift 2174860
  have htrace : WordTrace (prefixWord ++ tailWord_2174860) baseStart_2174860 baseEnd_2174860 := by
    simpa [prefixWord, tailWord_2174860, baseEnd_2174860] using wordTrace_append hprefix tailTrace_2174860
  have hstable : (prefixWord ++ tailWord_2174860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174860).length < 2 ^ (prefixWord ++ tailWord_2174860).sum := by decide
  have hdescent : baseEnd_2174860 < baseStart_2174860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174877 : List Nat := [1, 4, 2, 1, 2, 3, 3, 1, 1, 1, 4]
def baseStart_2174877 : Nat := 118140960795 + 2174877 * 2 ^ 59
def prefixEnd_2174877 : Nat := 4983230072969 + 3 ^ 40 * 2174877 * 2
def baseEnd_2174877 : Nat := 1116757265408592517435429

theorem tailTrace_2174877 : CollatzResearch.WordTrace tailWord_2174877 prefixEnd_2174877 1116757265408592517435429 := by
  unfold tailWord_2174877
  simp only [CollatzResearch.WordTrace]
  refine ⟨79324280941799543264906885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52882853961199695509937923 79324280941799543264906885)
  ·
    refine ⟨14873302676587414362170041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79324280941799543264906885 14873302676587414362170041)
    ·
      refine ⟨11154977007440560771627531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14873302676587414362170041 11154977007440560771627531)
      ·
        refine ⟨16732465511160841157441297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11154977007440560771627531 16732465511160841157441297)
        ·
          refine ⟨12549349133370630868080973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16732465511160841157441297 12549349133370630868080973)
          ·
            refine ⟨4706005925013986575530365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12549349133370630868080973 4706005925013986575530365)
            ·
              refine ⟨1764752221880244965823887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4706005925013986575530365 1764752221880244965823887)
              ·
                refine ⟨2647128332820367448735831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1764752221880244965823887 2647128332820367448735831)
                ·
                  refine ⟨3970692499230551173103747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2647128332820367448735831 3970692499230551173103747)
                  ·
                    refine ⟨5956038748845826759655621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3970692499230551173103747 5956038748845826759655621)
                    ·
                      refine ⟨1116757265408592517435429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5956038748845826759655621 1116757265408592517435429)
                      ·
                        rfl

theorem cell23_2174877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 1, 1, 1, 4].length) (baseStart_2174877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2174877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2174877 prefixEnd_2174877 := by exact prefixLift 2174877
  have htrace : WordTrace (prefixWord ++ tailWord_2174877) baseStart_2174877 baseEnd_2174877 := by
    simpa [prefixWord, tailWord_2174877, baseEnd_2174877] using wordTrace_append hprefix tailTrace_2174877
  have hstable : (prefixWord ++ tailWord_2174877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174877).length < 2 ^ (prefixWord ++ tailWord_2174877).sum := by decide
  have hdescent : baseEnd_2174877 < baseStart_2174877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174887 : List Nat := [1, 1, 6, 1, 2, 2, 2, 2, 2, 4]
def baseStart_2174887 : Nat := 118140960795 + 2174887 * 2 ^ 59
def prefixEnd_2174887 : Nat := 4983230072969 + 3 ^ 40 * 2174887 * 2
def baseEnd_2174887 : Nat := 372254133405045826103461

theorem tailTrace_2174887 : CollatzResearch.WordTrace tailWord_2174887 prefixEnd_2174887 372254133405045826103461 := by
  unfold tailWord_2174887
  simp only [CollatzResearch.WordTrace]
  refine ⟨79324645671763314972770915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52883097114508876648513943 79324645671763314972770915)
  ·
    refine ⟨118986968507644972459156373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79324645671763314972770915 118986968507644972459156373)
    ·
      refine ⟨5577514148795858084022955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 118986968507644972459156373 5577514148795858084022955)
      ·
        refine ⟨8366271223193787126034433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5577514148795858084022955 8366271223193787126034433)
        ·
          refine ⟨6274703417395340344525825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8366271223193787126034433 6274703417395340344525825)
          ·
            refine ⟨4706027563046505258394369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6274703417395340344525825 4706027563046505258394369)
            ·
              refine ⟨3529520672284878943795777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4706027563046505258394369 3529520672284878943795777)
              ·
                refine ⟨2647140504213659207846833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3529520672284878943795777 2647140504213659207846833)
                ·
                  refine ⟨1985355378160244405885125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2647140504213659207846833 1985355378160244405885125)
                  ·
                    refine ⟨372254133405045826103461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1985355378160244405885125 372254133405045826103461)
                    ·
                      rfl

theorem cell23_2174887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_2174887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2174887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2174887 prefixEnd_2174887 := by exact prefixLift 2174887
  have htrace : WordTrace (prefixWord ++ tailWord_2174887) baseStart_2174887 baseEnd_2174887 := by
    simpa [prefixWord, tailWord_2174887, baseEnd_2174887] using wordTrace_append hprefix tailTrace_2174887
  have hstable : (prefixWord ++ tailWord_2174887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174887).length < 2 ^ (prefixWord ++ tailWord_2174887).sum := by decide
  have hdescent : baseEnd_2174887 < baseStart_2174887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174910 : List Nat := [4, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3]
def baseStart_2174910 : Nat := 118140960795 + 2174910 * 2 ^ 59
def prefixEnd_2174910 : Nat := 4983230072969 + 3 ^ 40 * 2174910 * 2
def baseEnd_2174910 : Nat := 1116774210270190888322777

theorem tailTrace_2174910 : CollatzResearch.WordTrace tailWord_2174910 prefixEnd_2174910 1116774210270190888322777 := by
  unfold tailWord_2174910
  simp only [CollatzResearch.WordTrace]
  refine ⟨9915685568834998737607273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52883656367119993267238789 9915685568834998737607273)
  ·
    refine ⟨7436764176626249053205455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9915685568834998737607273 7436764176626249053205455)
    ·
      refine ⟨11155146264939373579808183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7436764176626249053205455 11155146264939373579808183)
      ·
        refine ⟨16732719397409060369712275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11155146264939373579808183 16732719397409060369712275)
        ·
          refine ⟨25099079096113590554568413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16732719397409060369712275 25099079096113590554568413)
          ·
            refine ⟨9412154661042596457963155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25099079096113590554568413 9412154661042596457963155)
            ·
              refine ⟨14118231991563894686944733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9412154661042596457963155 14118231991563894686944733)
              ·
                refine ⟨5294336996836460507604275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14118231991563894686944733 5294336996836460507604275)
                ·
                  refine ⟨7941505495254690761406413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5294336996836460507604275 7941505495254690761406413)
                  ·
                    refine ⟨2978064560720509035527405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7941505495254690761406413 2978064560720509035527405)
                    ·
                      refine ⟨1116774210270190888322777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2978064560720509035527405 1116774210270190888322777)
                      ·
                        rfl

theorem cell23_2174910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_2174910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2174910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2174910 prefixEnd_2174910 := by exact prefixLift 2174910
  have htrace : WordTrace (prefixWord ++ tailWord_2174910) baseStart_2174910 baseEnd_2174910 := by
    simpa [prefixWord, tailWord_2174910, baseEnd_2174910] using wordTrace_append hprefix tailTrace_2174910
  have hstable : (prefixWord ++ tailWord_2174910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174910).length < 2 ^ (prefixWord ++ tailWord_2174910).sum := by decide
  have hdescent : baseEnd_2174910 < baseStart_2174910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174943 : List Nat := [1, 1, 2, 3, 4, 1, 1, 2, 2, 6]
def baseStart_2174943 : Nat := 118140960795 + 2174943 * 2 ^ 59
def prefixEnd_2174943 : Nat := 4983230072969 + 3 ^ 40 * 2174943 * 2
def baseEnd_2174943 : Nat := 372263718377263086403375

theorem tailTrace_2174943 : CollatzResearch.WordTrace tailWord_2174943 prefixEnd_2174943 372263718377263086403375 := by
  unfold tailWord_2174943
  simp only [CollatzResearch.WordTrace]
  refine ⟨79326688159560436536809483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52884458773040291024539655 79326688159560436536809483)
  ·
    refine ⟨118990032239340654805214225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79326688159560436536809483 118990032239340654805214225)
    ·
      refine ⟨89242524179505491103910669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118990032239340654805214225 89242524179505491103910669)
      ·
        refine ⟨33465946567314559163966501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89242524179505491103910669 33465946567314559163966501)
        ·
          refine ⟨6274864981371479843243719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33465946567314559163966501 6274864981371479843243719)
          ·
            refine ⟨9412297472057219764865579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6274864981371479843243719 9412297472057219764865579)
            ·
              refine ⟨14118446208085829647298369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9412297472057219764865579 14118446208085829647298369)
              ·
                refine ⟨10588834656064372235473777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14118446208085829647298369 10588834656064372235473777)
                ·
                  refine ⟨7941625992048279176605333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10588834656064372235473777 7941625992048279176605333)
                  ·
                    refine ⟨372263718377263086403375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7941625992048279176605333 372263718377263086403375)
                    ·
                      rfl

theorem cell23_2174943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 2, 6].length) (baseStart_2174943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2174943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2174943 prefixEnd_2174943 := by exact prefixLift 2174943
  have htrace : WordTrace (prefixWord ++ tailWord_2174943) baseStart_2174943 baseEnd_2174943 := by
    simpa [prefixWord, tailWord_2174943, baseEnd_2174943] using wordTrace_append hprefix tailTrace_2174943
  have hstable : (prefixWord ++ tailWord_2174943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174943).length < 2 ^ (prefixWord ++ tailWord_2174943).sum := by decide
  have hdescent : baseEnd_2174943 < baseStart_2174943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174973 : List Nat := [1, 4, 1, 1, 1, 2, 4, 2, 7]
def baseStart_2174973 : Nat := 118140960795 + 2174973 * 2 ^ 59
def prefixEnd_2174973 : Nat := 4983230072969 + 3 ^ 40 * 2174973 * 2
def baseEnd_2174973 : Nat := 124089617727936015759443

theorem tailTrace_2174973 : CollatzResearch.WordTrace tailWord_2174973 prefixEnd_2174973 124089617727936015759443 := by
  unfold tailWord_2174973
  simp only [CollatzResearch.WordTrace]
  refine ⟨79327782349451751660401573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52885188232967834440267715 79327782349451751660401573)
  ·
    refine ⟨14873959190522203436325295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79327782349451751660401573 14873959190522203436325295)
    ·
      refine ⟨22310938785783305154487943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14873959190522203436325295 22310938785783305154487943)
      ·
        refine ⟨33466408178674957731731915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22310938785783305154487943 33466408178674957731731915)
        ·
          refine ⟨50199612268012436597597873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33466408178674957731731915 50199612268012436597597873)
          ·
            refine ⟨37649709201009327448198405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50199612268012436597597873 37649709201009327448198405)
            ·
              refine ⟨7059320475189248896537201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37649709201009327448198405 7059320475189248896537201)
              ·
                refine ⟨5294490356391936672402901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7059320475189248896537201 5294490356391936672402901)
                ·
                  refine ⟨124089617727936015759443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5294490356391936672402901 124089617727936015759443)
                  ·
                    rfl

theorem cell23_2174973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2, 7].length) (baseStart_2174973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2174973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2174973 prefixEnd_2174973 := by exact prefixLift 2174973
  have htrace : WordTrace (prefixWord ++ tailWord_2174973) baseStart_2174973 baseEnd_2174973 := by
    simpa [prefixWord, tailWord_2174973, baseEnd_2174973] using wordTrace_append hprefix tailTrace_2174973
  have hstable : (prefixWord ++ tailWord_2174973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174973).length < 2 ^ (prefixWord ++ tailWord_2174973).sum := by decide
  have hdescent : baseEnd_2174973 < baseStart_2174973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175007 : List Nat := [1, 1, 2, 4, 1, 2, 5, 2, 5]
def baseStart_2175007 : Nat := 118140960795 + 2175007 * 2 ^ 59
def prefixEnd_2175007 : Nat := 4983230072969 + 3 ^ 40 * 2175007 * 2
def baseEnd_2175007 : Nat := 124091557543741889867759

theorem tailTrace_2175007 : CollatzResearch.WordTrace tailWord_2175007 prefixEnd_2175007 124091557543741889867759 := by
  unfold tailWord_2175007
  simp only [CollatzResearch.WordTrace]
  refine ⟨79329022431328575467139275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52886014954219050311426183 79329022431328575467139275)
  ·
    refine ⟨118993533646992863200708913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79329022431328575467139275 118993533646992863200708913)
    ·
      refine ⟨89245150235244647400531685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118993533646992863200708913 89245150235244647400531685)
      ·
        refine ⟨16733465669108371387599691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89245150235244647400531685 16733465669108371387599691)
        ·
          refine ⟨25100198503662557081399537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16733465669108371387599691 25100198503662557081399537)
          ·
            refine ⟨18825148877746917811049653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25100198503662557081399537 18825148877746917811049653)
            ·
              refine ⟨1764857707288773544785905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18825148877746917811049653 1764857707288773544785905)
              ·
                refine ⟨1323643280466580158589429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1764857707288773544785905 1323643280466580158589429)
                ·
                  refine ⟨124091557543741889867759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1323643280466580158589429 124091557543741889867759)
                  ·
                    rfl

theorem cell23_2175007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 2, 5].length) (baseStart_2175007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2175007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2175007 prefixEnd_2175007 := by exact prefixLift 2175007
  have htrace : WordTrace (prefixWord ++ tailWord_2175007) baseStart_2175007 baseEnd_2175007 := by
    simpa [prefixWord, tailWord_2175007, baseEnd_2175007] using wordTrace_append hprefix tailTrace_2175007
  have hstable : (prefixWord ++ tailWord_2175007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175007).length < 2 ^ (prefixWord ++ tailWord_2175007).sum := by decide
  have hdescent : baseEnd_2175007 < baseStart_2175007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175013 : List Nat := [1, 3, 1, 2, 2, 3, 1, 1, 1, 1, 7]
def baseStart_2175013 : Nat := 118140960795 + 2175013 * 2 ^ 59
def prefixEnd_2175013 : Nat := 4983230072969 + 3 ^ 40 * 2175013 * 2
def baseEnd_2175013 : Nat := 1116827098777603985334803

theorem tailTrace_2175013 : CollatzResearch.WordTrace tailWord_2175013 prefixEnd_2175013 1116827098777603985334803 := by
  unfold tailWord_2175013
  simp only [CollatzResearch.WordTrace]
  refine ⟨79329241269306838491857693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52886160846204558994571795 79329241269306838491857693)
  ·
    refine ⟨29748465475990064434446635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79329241269306838491857693 29748465475990064434446635)
    ·
      refine ⟨44622698213985096651669953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29748465475990064434446635 44622698213985096651669953)
      ·
        refine ⟨33467023660488822488752465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44622698213985096651669953 33467023660488822488752465)
        ·
          refine ⟨25100267745366616866564349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33467023660488822488752465 25100267745366616866564349)
          ·
            refine ⟨9412600404512481324961631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25100267745366616866564349 9412600404512481324961631)
            ·
              refine ⟨14118900606768721987442447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9412600404512481324961631 14118900606768721987442447)
              ·
                refine ⟨21178350910153082981163671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14118900606768721987442447 21178350910153082981163671)
                ·
                  refine ⟨31767526365229624471745507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21178350910153082981163671 31767526365229624471745507)
                  ·
                    refine ⟨47651289547844436707618261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31767526365229624471745507 47651289547844436707618261)
                    ·
                      refine ⟨1116827098777603985334803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 47651289547844436707618261 1116827098777603985334803)
                      ·
                        rfl

theorem cell23_2175013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_2175013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2175013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2175013 prefixEnd_2175013 := by exact prefixLift 2175013
  have htrace : WordTrace (prefixWord ++ tailWord_2175013) baseStart_2175013 baseEnd_2175013 := by
    simpa [prefixWord, tailWord_2175013, baseEnd_2175013] using wordTrace_append hprefix tailTrace_2175013
  have hstable : (prefixWord ++ tailWord_2175013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175013).length < 2 ^ (prefixWord ++ tailWord_2175013).sum := by decide
  have hdescent : baseEnd_2175013 < baseStart_2175013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175018 : List Nat := [3, 1, 4, 1, 2, 3, 2, 1, 2, 2, 2]
def baseStart_2175018 : Nat := 118140960795 + 2175018 * 2 ^ 59
def prefixEnd_2175018 : Nat := 4983230072969 + 3 ^ 40 * 2175018 * 2
def baseEnd_2175018 : Nat := 1116829666180876465772281

theorem tailTrace_2175018 : CollatzResearch.WordTrace tailWord_2175018 prefixEnd_2175018 1116829666180876465772281 := by
  unfold tailWord_2175018
  simp only [CollatzResearch.WordTrace]
  refine ⟨19832355908572181086447427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52886282422859149563859805 19832355908572181086447427)
  ·
    refine ⟨29748533862858271629671141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19832355908572181086447427 29748533862858271629671141)
    ·
      refine ⟨5577850099285925930563339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29748533862858271629671141 5577850099285925930563339)
      ·
        refine ⟨8366775148928888895845009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5577850099285925930563339 8366775148928888895845009)
        ·
          refine ⟨6275081361696666671883757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8366775148928888895845009 6275081361696666671883757)
          ·
            refine ⟨2353155510636250001956409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6275081361696666671883757 2353155510636250001956409)
            ·
              refine ⟨1764866632977187501467307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2353155510636250001956409 1764866632977187501467307)
              ·
                refine ⟨2647299949465781252200961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1764866632977187501467307 2647299949465781252200961)
                ·
                  refine ⟨1985474962099335939150721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2647299949465781252200961 1985474962099335939150721)
                  ·
                    refine ⟨1489106221574501954363041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1985474962099335939150721 1489106221574501954363041)
                    ·
                      refine ⟨1116829666180876465772281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1489106221574501954363041 1116829666180876465772281)
                      ·
                        rfl

theorem cell23_2175018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_2175018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2175018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2175018 prefixEnd_2175018 := by exact prefixLift 2175018
  have htrace : WordTrace (prefixWord ++ tailWord_2175018) baseStart_2175018 baseEnd_2175018 := by
    simpa [prefixWord, tailWord_2175018, baseEnd_2175018] using wordTrace_append hprefix tailTrace_2175018
  have hstable : (prefixWord ++ tailWord_2175018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175018).length < 2 ^ (prefixWord ++ tailWord_2175018).sum := by decide
  have hdescent : baseEnd_2175018 < baseStart_2175018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175023 : List Nat := [1, 1, 2, 1, 2, 1, 1, 6, 1, 3, 4]
def baseStart_2175023 : Nat := 118140960795 + 2175023 * 2 ^ 59
def prefixEnd_2175023 : Nat := 4983230072969 + 3 ^ 40 * 2175023 * 2
def baseEnd_2175023 : Nat := 1116832233584148946209757

theorem tailTrace_2175023 : CollatzResearch.WordTrace tailWord_2175023 prefixEnd_2175023 1116832233584148946209757 := by
  unfold tailWord_2175023
  simp only [CollatzResearch.WordTrace]
  refine ⟨79329605999270610199721723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52886403999513740133147815 79329605999270610199721723)
  ·
    refine ⟨118994408998905915299582585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79329605999270610199721723 118994408998905915299582585)
    ·
      refine ⟨89245806749179436474686939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118994408998905915299582585 89245806749179436474686939)
      ·
        refine ⟨133868710123769154712030409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89245806749179436474686939 133868710123769154712030409)
        ·
          refine ⟨100401532592826866034022807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133868710123769154712030409 100401532592826866034022807)
          ·
            refine ⟨150602298889240299051034211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100401532592826866034022807 150602298889240299051034211)
            ·
              refine ⟨225903448333860448576551317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150602298889240299051034211 225903448333860448576551317)
              ·
                refine ⟨10589224140649708527025843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 225903448333860448576551317 10589224140649708527025843)
                ·
                  refine ⟨15883836210974562790538765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10589224140649708527025843 15883836210974562790538765)
                  ·
                    refine ⟨5956438579115461046452037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15883836210974562790538765 5956438579115461046452037)
                    ·
                      refine ⟨1116832233584148946209757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5956438579115461046452037 1116832233584148946209757)
                      ·
                        rfl

theorem cell23_2175023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 3, 4].length) (baseStart_2175023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2175023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2175023 prefixEnd_2175023 := by exact prefixLift 2175023
  have htrace : WordTrace (prefixWord ++ tailWord_2175023) baseStart_2175023 baseEnd_2175023 := by
    simpa [prefixWord, tailWord_2175023, baseEnd_2175023] using wordTrace_append hprefix tailTrace_2175023
  have hstable : (prefixWord ++ tailWord_2175023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175023).length < 2 ^ (prefixWord ++ tailWord_2175023).sum := by decide
  have hdescent : baseEnd_2175023 < baseStart_2175023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175030 : List Nat := [5, 1, 2, 1, 1, 1, 1, 2, 1, 1, 7]
def baseStart_2175030 : Nat := 118140960795 + 2175030 * 2 ^ 59
def prefixEnd_2175030 : Nat := 4983230072969 + 3 ^ 40 * 2175030 * 2
def baseEnd_2175030 : Nat := 1116835827948730418822225

theorem tailTrace_2175030 : CollatzResearch.WordTrace tailWord_2175030 prefixEnd_2175030 1116835827948730418822225 := by
  unfold tailWord_2175030
  simp only [CollatzResearch.WordTrace]
  refine ⟨4958116331890328149701659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52886574206830166930151029 4958116331890328149701659)
  ·
    refine ⟨7437174497835492224552489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4958116331890328149701659 7437174497835492224552489)
    ·
      refine ⟨5577880873376619168414367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7437174497835492224552489 5577880873376619168414367)
      ·
        refine ⟨8366821310064928752621551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5577880873376619168414367 8366821310064928752621551)
        ·
          refine ⟨12550231965097393128932327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8366821310064928752621551 12550231965097393128932327)
          ·
            refine ⟨18825347947646089693398491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12550231965097393128932327 18825347947646089693398491)
            ·
              refine ⟨28238021921469134540097737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18825347947646089693398491 28238021921469134540097737)
              ·
                refine ⟨21178516441101850905073303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28238021921469134540097737 21178516441101850905073303)
                ·
                  refine ⟨31767774661652776357609955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21178516441101850905073303 31767774661652776357609955)
                  ·
                    refine ⟨47651661992479164536414933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31767774661652776357609955 47651661992479164536414933)
                    ·
                      refine ⟨1116835827948730418822225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 47651661992479164536414933 1116835827948730418822225)
                      ·
                        rfl

theorem cell23_2175030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_2175030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2175030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2175030 prefixEnd_2175030 := by exact prefixLift 2175030
  have htrace : WordTrace (prefixWord ++ tailWord_2175030) baseStart_2175030 baseEnd_2175030 := by
    simpa [prefixWord, tailWord_2175030, baseEnd_2175030] using wordTrace_append hprefix tailTrace_2175030
  have hstable : (prefixWord ++ tailWord_2175030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175030).length < 2 ^ (prefixWord ++ tailWord_2175030).sum := by decide
  have hdescent : baseEnd_2175030 < baseStart_2175030 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175040 : List Nat := [2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 4]
def baseStart_2175040 : Nat := 118140960795 + 2175040 * 2 ^ 59
def prefixEnd_2175040 : Nat := 4983230072969 + 3 ^ 40 * 2175040 * 2
def baseEnd_2175040 : Nat := 1116840962755275379697179

theorem tailTrace_2175040 : CollatzResearch.WordTrace tailWord_2175040 prefixEnd_2175040 1116840962755275379697179 := by
  unfold tailWord_2175040
  simp only [CollatzResearch.WordTrace]
  refine ⟨39665113020104511051545287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52886817360139348068727049 39665113020104511051545287)
  ·
    refine ⟨59497669530156766577317931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39665113020104511051545287 59497669530156766577317931)
    ·
      refine ⟨89246504295235149865976897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59497669530156766577317931 89246504295235149865976897)
      ·
        refine ⟨66934878221426362399482673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89246504295235149865976897 66934878221426362399482673)
        ·
          refine ⟨50201158666069771799612005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66934878221426362399482673 50201158666069771799612005)
          ·
            refine ⟨9412717249888082212427251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50201158666069771799612005 9412717249888082212427251)
            ·
              refine ⟨14119075874832123318640877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9412717249888082212427251 14119075874832123318640877)
              ·
                refine ⟨5294653453062046244490329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14119075874832123318640877 5294653453062046244490329)
                ·
                  refine ⟨3970990089796534683367747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5294653453062046244490329 3970990089796534683367747)
                  ·
                    refine ⟨5956485134694802025051621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3970990089796534683367747 5956485134694802025051621)
                    ·
                      refine ⟨1116840962755275379697179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5956485134694802025051621 1116840962755275379697179)
                      ·
                        rfl

theorem cell23_2175040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 4].length) (baseStart_2175040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2175040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2175040 prefixEnd_2175040 := by exact prefixLift 2175040
  have htrace : WordTrace (prefixWord ++ tailWord_2175040) baseStart_2175040 baseEnd_2175040 := by
    simpa [prefixWord, tailWord_2175040, baseEnd_2175040] using wordTrace_append hprefix tailTrace_2175040
  have hstable : (prefixWord ++ tailWord_2175040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175040).length < 2 ^ (prefixWord ++ tailWord_2175040).sum := by decide
  have hdescent : baseEnd_2175040 < baseStart_2175040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175060 : List Nat := [2, 4, 1, 1, 1, 1, 1, 2, 3, 4, 3]
def baseStart_2175060 : Nat := 118140960795 + 2175060 * 2 ^ 59
def prefixEnd_2175060 : Nat := 4983230072969 + 3 ^ 40 * 2175060 * 2
def baseEnd_2175060 : Nat := 1116851232368365301447087

theorem tailTrace_2175060 : CollatzResearch.WordTrace tailWord_2175060 prefixEnd_2175060 1116851232368365301447087 := by
  unfold tailWord_2175060
  simp only [CollatzResearch.WordTrace]
  refine ⟨39665477750068282759409317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52887303666757710345879089 39665477750068282759409317)
  ·
    refine ⟨7437277078137803017389247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39665477750068282759409317 7437277078137803017389247)
    ·
      refine ⟨11155915617206704526083871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7437277078137803017389247 11155915617206704526083871)
      ·
        refine ⟨16733873425810056789125807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11155915617206704526083871 16733873425810056789125807)
        ·
          refine ⟨25100810138715085183688711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16733873425810056789125807 25100810138715085183688711)
          ·
            refine ⟨37651215208072627775533067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25100810138715085183688711 37651215208072627775533067)
            ·
              refine ⟨56476822812108941663299601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37651215208072627775533067 56476822812108941663299601)
              ·
                refine ⟨42357617109081706247474701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56476822812108941663299601 42357617109081706247474701)
                ·
                  refine ⟨15884106415905639842803013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42357617109081706247474701 15884106415905639842803013)
                  ·
                    refine ⟨2978269952982307470525565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15884106415905639842803013 2978269952982307470525565)
                    ·
                      refine ⟨1116851232368365301447087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2978269952982307470525565 1116851232368365301447087)
                      ·
                        rfl

theorem cell23_2175060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_2175060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2175060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2175060 prefixEnd_2175060 := by exact prefixLift 2175060
  have htrace : WordTrace (prefixWord ++ tailWord_2175060) baseStart_2175060 baseEnd_2175060 := by
    simpa [prefixWord, tailWord_2175060, baseEnd_2175060] using wordTrace_append hprefix tailTrace_2175060
  have hstable : (prefixWord ++ tailWord_2175060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175060).length < 2 ^ (prefixWord ++ tailWord_2175060).sum := by decide
  have hdescent : baseEnd_2175060 < baseStart_2175060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175063 : List Nat := [1, 1, 3, 2, 2, 1, 2, 3, 8]
def baseStart_2175063 : Nat := 118140960795 + 2175063 * 2 ^ 59
def prefixEnd_2175063 : Nat := 4983230072969 + 3 ^ 40 * 2175063 * 2
def baseEnd_2175063 : Nat := 124094752534480976634397

theorem tailTrace_2175063 : CollatzResearch.WordTrace tailWord_2175063 prefixEnd_2175063 124094752534480976634397 := by
  unfold tailWord_2175063
  simp only [CollatzResearch.WordTrace]
  refine ⟨79331064919125697031177843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52887376612750464687451895 79331064919125697031177843)
  ·
    refine ⟨118996597378688545546766765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79331064919125697031177843 118996597378688545546766765)
    ·
      refine ⟨44623724017008204580037537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118996597378688545546766765 44623724017008204580037537)
      ·
        refine ⟨33467793012756153435028153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44623724017008204580037537 33467793012756153435028153)
        ·
          refine ⟨25100844759567115076271115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33467793012756153435028153 25100844759567115076271115)
          ·
            refine ⟨37651267139350672614406673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25100844759567115076271115 37651267139350672614406673)
            ·
              refine ⟨28238450354513004460805005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37651267139350672614406673 28238450354513004460805005)
              ·
                refine ⟨10589418882942376672801877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28238450354513004460805005 10589418882942376672801877)
                ·
                  refine ⟨124094752534480976634397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10589418882942376672801877 124094752534480976634397)
                  ·
                    rfl

theorem cell23_2175063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 8].length) (baseStart_2175063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2175063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2175063 prefixEnd_2175063 := by exact prefixLift 2175063
  have htrace : WordTrace (prefixWord ++ tailWord_2175063) baseStart_2175063 baseEnd_2175063 := by
    simpa [prefixWord, tailWord_2175063, baseEnd_2175063] using wordTrace_append hprefix tailTrace_2175063
  have hstable : (prefixWord ++ tailWord_2175063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175063).length < 2 ^ (prefixWord ++ tailWord_2175063).sum := by decide
  have hdescent : baseEnd_2175063 < baseStart_2175063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175094 : List Nat := [5, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3]
def baseStart_2175094 : Nat := 118140960795 + 2175094 * 2 ^ 59
def prefixEnd_2175094 : Nat := 4983230072969 + 3 ^ 40 * 2175094 * 2
def baseEnd_2175094 : Nat := 1116868690710618168421931

theorem tailTrace_2175094 : CollatzResearch.WordTrace tailWord_2175094 prefixEnd_2175094 1116868690710618168421931 := by
  unfold tailWord_2175094
  simp only [CollatzResearch.WordTrace]
  refine ⟨4958262223875836832847271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52888130388008926217037557 4958262223875836832847271)
  ·
    refine ⟨7437393335813755249270907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4958262223875836832847271 7437393335813755249270907)
    ·
      refine ⟨11156090003720632873906361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7437393335813755249270907 11156090003720632873906361)
      ·
        refine ⟨8367067502790474655429771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11156090003720632873906361 8367067502790474655429771)
        ·
          refine ⟨12550601254185711983144657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8367067502790474655429771 12550601254185711983144657)
          ·
            refine ⟨9412950940639283987358493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12550601254185711983144657 9412950940639283987358493)
            ·
              refine ⟨3529856602739731495259435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9412950940639283987358493 3529856602739731495259435)
              ·
                refine ⟨5294784904109597242889153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3529856602739731495259435 5294784904109597242889153)
                ·
                  refine ⟨3971088678082197932166865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5294784904109597242889153 3971088678082197932166865)
                  ·
                    refine ⟨2978316508561648449125149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3971088678082197932166865 2978316508561648449125149)
                    ·
                      refine ⟨1116868690710618168421931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2978316508561648449125149 1116868690710618168421931)
                      ·
                        rfl

theorem cell23_2175094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_2175094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2175094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2175094 prefixEnd_2175094 := by exact prefixLift 2175094
  have htrace : WordTrace (prefixWord ++ tailWord_2175094) baseStart_2175094 baseEnd_2175094 := by
    simpa [prefixWord, tailWord_2175094, baseEnd_2175094] using wordTrace_append hprefix tailTrace_2175094
  have hstable : (prefixWord ++ tailWord_2175094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175094).length < 2 ^ (prefixWord ++ tailWord_2175094).sum := by decide
  have hdescent : baseEnd_2175094 < baseStart_2175094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175160 : List Nat := [2, 1, 2, 1, 2, 1, 4, 1, 3, 2, 4]
def baseStart_2175160 : Nat := 118140960795 + 2175160 * 2 ^ 59
def prefixEnd_2175160 : Nat := 4983230072969 + 3 ^ 40 * 2175160 * 2
def baseEnd_2175160 : Nat := 1116902580433814910196627

theorem tailTrace_2175160 : CollatzResearch.WordTrace tailWord_2175160 prefixEnd_2175160 1116902580433814910196627 := by
  unfold tailWord_2175160
  simp only [CollatzResearch.WordTrace]
  refine ⟨39667301399887141298729467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52889735199849521731639289 39667301399887141298729467)
  ·
    refine ⟨59500952099830711948094201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39667301399887141298729467 59500952099830711948094201)
    ·
      refine ⟨44625714074873033961070651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59500952099830711948094201 44625714074873033961070651)
      ·
        refine ⟨66938571112309550941605977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44625714074873033961070651 66938571112309550941605977)
        ·
          refine ⟨50203928334232163206204483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66938571112309550941605977 50203928334232163206204483)
          ·
            refine ⟨75305892501348244809306725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50203928334232163206204483 75305892501348244809306725)
            ·
              refine ⟨14119854844002795901745011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75305892501348244809306725 14119854844002795901745011)
              ·
                refine ⟨21179782266004193852617517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14119854844002795901745011 21179782266004193852617517)
                ·
                  refine ⟨7942418349751572694731569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21179782266004193852617517 7942418349751572694731569)
                  ·
                    refine ⟨5956813762313679521048677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7942418349751572694731569 5956813762313679521048677)
                    ·
                      refine ⟨1116902580433814910196627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5956813762313679521048677 1116902580433814910196627)
                      ·
                        rfl

theorem cell23_2175160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 3, 2, 4].length) (baseStart_2175160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2175160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2175160 prefixEnd_2175160 := by exact prefixLift 2175160
  have htrace : WordTrace (prefixWord ++ tailWord_2175160) baseStart_2175160 baseEnd_2175160 := by
    simpa [prefixWord, tailWord_2175160, baseEnd_2175160] using wordTrace_append hprefix tailTrace_2175160
  have hstable : (prefixWord ++ tailWord_2175160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175160).length < 2 ^ (prefixWord ++ tailWord_2175160).sum := by decide
  have hdescent : baseEnd_2175160 < baseStart_2175160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175224 : List Nat := [2, 1, 2, 1, 1, 2, 1, 7, 1, 3, 2]
def baseStart_2175224 : Nat := 118140960795 + 2175224 * 2 ^ 59
def prefixEnd_2175224 : Nat := 4983230072969 + 3 ^ 40 * 2175224 * 2
def baseEnd_2175224 : Nat := 1116935443195702659796333

theorem tailTrace_2175224 : CollatzResearch.WordTrace tailWord_2175224 prefixEnd_2175224 1116935443195702659796333 := by
  unfold tailWord_2175224
  simp only [CollatzResearch.WordTrace]
  refine ⟨39668468535771210763894363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52891291381028281018525817 39668468535771210763894363)
  ·
    refine ⟨59502702803656816145841545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39668468535771210763894363 59502702803656816145841545)
    ·
      refine ⟨44627027102742612109381159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59502702803656816145841545 44627027102742612109381159)
      ·
        refine ⟨66940540654113918164071739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44627027102742612109381159 66940540654113918164071739)
        ·
          refine ⟨100410810981170877246107609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66940540654113918164071739 100410810981170877246107609)
          ·
            refine ⟨75308108235878157934580707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100410810981170877246107609 75308108235878157934580707)
            ·
              refine ⟨112962162353817236901871061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75308108235878157934580707 112962162353817236901871061)
              ·
                refine ⟨2647550680167591489887603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 112962162353817236901871061 2647550680167591489887603)
                ·
                  refine ⟨3971326020251387234831405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2647550680167591489887603 3971326020251387234831405)
                  ·
                    refine ⟨1489247257594270213061777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3971326020251387234831405 1489247257594270213061777)
                    ·
                      refine ⟨1116935443195702659796333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1489247257594270213061777 1116935443195702659796333)
                      ·
                        rfl

theorem cell23_2175224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 7, 1, 3, 2].length) (baseStart_2175224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2175224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2175224 prefixEnd_2175224 := by exact prefixLift 2175224
  have htrace : WordTrace (prefixWord ++ tailWord_2175224) baseStart_2175224 baseEnd_2175224 := by
    simpa [prefixWord, tailWord_2175224, baseEnd_2175224] using wordTrace_append hprefix tailTrace_2175224
  have hstable : (prefixWord ++ tailWord_2175224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175224).length < 2 ^ (prefixWord ++ tailWord_2175224).sum := by decide
  have hdescent : baseEnd_2175224 < baseStart_2175224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175284 : List Nat := [2, 5, 1, 1, 1, 2, 1, 2, 2, 2, 4]
def baseStart_2175284 : Nat := 118140960795 + 2175284 * 2 ^ 59
def prefixEnd_2175284 : Nat := 4983230072969 + 3 ^ 40 * 2175284 * 2
def baseEnd_2175284 : Nat := 1116966252034972425046057

theorem tailTrace_2175284 : CollatzResearch.WordTrace tailWord_2175284 prefixEnd_2175284 1116966252034972425046057 := by
  unfold tailWord_2175284
  simp only [CollatzResearch.WordTrace]
  refine ⟨39669562725662525887486453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52892750300883367849981937 39669562725662525887486453)
  ·
    refine ⟨3719021505530861801951855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39669562725662525887486453 3719021505530861801951855)
    ·
      refine ⟨5578532258296292702927783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3719021505530861801951855 5578532258296292702927783)
      ·
        refine ⟨8367798387444439054391675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5578532258296292702927783 8367798387444439054391675)
        ·
          refine ⟨12551697581166658581587513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8367798387444439054391675 12551697581166658581587513)
          ·
            refine ⟨9413773185874993936190635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12551697581166658581587513 9413773185874993936190635)
            ·
              refine ⟨14120659778812490904285953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9413773185874993936190635 14120659778812490904285953)
              ·
                refine ⟨10590494834109368178214465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14120659778812490904285953 10590494834109368178214465)
                ·
                  refine ⟨7942871125582026133660849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10590494834109368178214465 7942871125582026133660849)
                  ·
                    refine ⟨5957153344186519600245637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7942871125582026133660849 5957153344186519600245637)
                    ·
                      refine ⟨1116966252034972425046057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5957153344186519600245637 1116966252034972425046057)
                      ·
                        rfl

theorem cell23_2175284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_2175284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2175284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2175284 prefixEnd_2175284 := by exact prefixLift 2175284
  have htrace : WordTrace (prefixWord ++ tailWord_2175284) baseStart_2175284 baseEnd_2175284 := by
    simpa [prefixWord, tailWord_2175284, baseEnd_2175284] using wordTrace_append hprefix tailTrace_2175284
  have hstable : (prefixWord ++ tailWord_2175284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175284).length < 2 ^ (prefixWord ++ tailWord_2175284).sum := by decide
  have hdescent : baseEnd_2175284 < baseStart_2175284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175294 : List Nat := [4, 2, 1, 2, 1, 3, 2, 1, 7]
def baseStart_2175294 : Nat := 118140960795 + 2175294 * 2 ^ 59
def prefixEnd_2175294 : Nat := 4983230072969 + 3 ^ 40 * 2175294 * 2
def baseEnd_2175294 : Nat := 124107931871279709546779

theorem tailTrace_2175294 : CollatzResearch.WordTrace tailWord_2175294 prefixEnd_2175294 124107931871279709546779 := by
  unfold tailWord_2175294
  simp only [CollatzResearch.WordTrace]
  refine ⟨9917436272661102935354617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52892993454192548988557957 9917436272661102935354617)
  ·
    refine ⟨7438077204495827201515963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9917436272661102935354617 7438077204495827201515963)
    ·
      refine ⟨11157115806743740802273945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7438077204495827201515963 11157115806743740802273945)
      ·
        refine ⟨8367836855057805601705459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11157115806743740802273945 8367836855057805601705459)
        ·
          refine ⟨12551755282586708402558189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8367836855057805601705459 12551755282586708402558189)
          ·
            refine ⟨4706908230970015650959321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12551755282586708402558189 4706908230970015650959321)
            ·
              refine ⟨3530181173227511738219491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4706908230970015650959321 3530181173227511738219491)
              ·
                refine ⟨5295271759841267607329237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3530181173227511738219491 5295271759841267607329237)
                ·
                  refine ⟨124107931871279709546779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5295271759841267607329237 124107931871279709546779)
                  ·
                    rfl

theorem cell23_2175294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 1, 7].length) (baseStart_2175294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2175294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2175294 prefixEnd_2175294 := by exact prefixLift 2175294
  have htrace : WordTrace (prefixWord ++ tailWord_2175294) baseStart_2175294 baseEnd_2175294 := by
    simpa [prefixWord, tailWord_2175294, baseEnd_2175294] using wordTrace_append hprefix tailTrace_2175294
  have hstable : (prefixWord ++ tailWord_2175294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175294).length < 2 ^ (prefixWord ++ tailWord_2175294).sum := by decide
  have hdescent : baseEnd_2175294 < baseStart_2175294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175314 : List Nat := [3, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2]
def baseStart_2175314 : Nat := 118140960795 + 2175314 * 2 ^ 59
def prefixEnd_2175314 : Nat := 4983230072969 + 3 ^ 40 * 2175314 * 2
def baseEnd_2175314 : Nat := 1116981656454607307670919

theorem tailTrace_2175314 : CollatzResearch.WordTrace tailWord_2175314 prefixEnd_2175314 1116981656454607307670919 := by
  unfold tailWord_2175314
  simp only [CollatzResearch.WordTrace]
  refine ⟨19835054910304091724641249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52893479760810911265709997 19835054910304091724641249)
  ·
    refine ⟨14876291182728068793480937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19835054910304091724641249 14876291182728068793480937)
    ·
      refine ⟨11157218387046051595110703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14876291182728068793480937 11157218387046051595110703)
      ·
        refine ⟨16735827580569077392666055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11157218387046051595110703 16735827580569077392666055)
        ·
          refine ⟨25103741370853616088999083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16735827580569077392666055 25103741370853616088999083)
          ·
            refine ⟨37655612056280424133498625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25103741370853616088999083 37655612056280424133498625)
            ·
              refine ⟨28241709042210318100123969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37655612056280424133498625 28241709042210318100123969)
              ·
                refine ⟨21181281781657738575092977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28241709042210318100123969 21181281781657738575092977)
                ·
                  refine ⟨15885961336243303931319733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21181281781657738575092977 15885961336243303931319733)
                  ·
                    refine ⟨1489308875272809743561225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15885961336243303931319733 1489308875272809743561225)
                    ·
                      refine ⟨1116981656454607307670919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1489308875272809743561225 1116981656454607307670919)
                      ·
                        rfl

theorem cell23_2175314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2].length) (baseStart_2175314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2175314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2175314 prefixEnd_2175314 := by exact prefixLift 2175314
  have htrace : WordTrace (prefixWord ++ tailWord_2175314) baseStart_2175314 baseEnd_2175314 := by
    simpa [prefixWord, tailWord_2175314, baseEnd_2175314] using wordTrace_append hprefix tailTrace_2175314
  have hstable : (prefixWord ++ tailWord_2175314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175314).length < 2 ^ (prefixWord ++ tailWord_2175314).sum := by decide
  have hdescent : baseEnd_2175314 < baseStart_2175314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175327 : List Nat := [1, 1, 2, 3, 1, 2, 4, 1, 1, 3, 4]
def baseStart_2175327 : Nat := 118140960795 + 2175327 * 2 ^ 59
def prefixEnd_2175327 : Nat := 4983230072969 + 3 ^ 40 * 2175327 * 2
def baseEnd_2175327 : Nat := 1116988331703115756808359

theorem tailTrace_2175327 : CollatzResearch.WordTrace tailWord_2175327 prefixEnd_2175327 1116988331703115756808359 := by
  unfold tailWord_2175327
  simp only [CollatzResearch.WordTrace]
  refine ⟨79340693790169270118788235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52893795860112846745858823 79340693790169270118788235)
  ·
    refine ⟨119011040685253905178182353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79340693790169270118788235 119011040685253905178182353)
    ·
      refine ⟨89258280513940428883636765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119011040685253905178182353 89258280513940428883636765)
      ·
        refine ⟨33471855192727660831363787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89258280513940428883636765 33471855192727660831363787)
        ·
          refine ⟨50207782789091491247045681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33471855192727660831363787 50207782789091491247045681)
          ·
            refine ⟨37655837091818618435284261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50207782789091491247045681 37655837091818618435284261)
            ·
              refine ⟨7060469454715990956615799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37655837091818618435284261 7060469454715990956615799)
              ·
                refine ⟨10590704182073986434923699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7060469454715990956615799 10590704182073986434923699)
                ·
                  refine ⟨15886056273110979652385549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10590704182073986434923699 15886056273110979652385549)
                  ·
                    refine ⟨5957271102416617369644581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15886056273110979652385549 5957271102416617369644581)
                    ·
                      refine ⟨1116988331703115756808359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5957271102416617369644581 1116988331703115756808359)
                      ·
                        rfl

theorem cell23_2175327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_2175327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2175327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2175327 prefixEnd_2175327 := by exact prefixLift 2175327
  have htrace : WordTrace (prefixWord ++ tailWord_2175327) baseStart_2175327 baseEnd_2175327 := by
    simpa [prefixWord, tailWord_2175327, baseEnd_2175327] using wordTrace_append hprefix tailTrace_2175327
  have hstable : (prefixWord ++ tailWord_2175327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175327).length < 2 ^ (prefixWord ++ tailWord_2175327).sum := by decide
  have hdescent : baseEnd_2175327 < baseStart_2175327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175328 : List Nat := [2, 1, 1, 3, 6, 1, 1, 3, 5]
def baseStart_2175328 : Nat := 118140960795 + 2175328 * 2 ^ 59
def prefixEnd_2175328 : Nat := 4983230072969 + 3 ^ 40 * 2175328 * 2
def baseEnd_2175328 : Nat := 124109871687085583655095

theorem tailTrace_2175328 : CollatzResearch.WordTrace tailWord_2175328 prefixEnd_2175328 124109871687085583655095 := by
  unfold tailWord_2175328
  simp only [CollatzResearch.WordTrace]
  refine ⟨39670365131582823644787319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52893820175443764859716425 39670365131582823644787319)
  ·
    refine ⟨59505547697374235467180979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39670365131582823644787319 59505547697374235467180979)
    ·
      refine ⟨89258321546061353200771469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59505547697374235467180979 89258321546061353200771469)
      ·
        refine ⟨33471870579773007450289301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89258321546061353200771469 33471870579773007450289301)
        ·
          refine ⟨1568993933426859724232311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 33471870579773007450289301 1568993933426859724232311)
          ·
            refine ⟨2353490900140289586348467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1568993933426859724232311 2353490900140289586348467)
            ·
              refine ⟨3530236350210434379522701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2353490900140289586348467 3530236350210434379522701)
              ·
                refine ⟨1323838631328912892321013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3530236350210434379522701 1323838631328912892321013)
                ·
                  refine ⟨124109871687085583655095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1323838631328912892321013 124109871687085583655095)
                  ·
                    rfl

theorem cell23_2175328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 3, 5].length) (baseStart_2175328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2175328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2175328 prefixEnd_2175328 := by exact prefixLift 2175328
  have htrace : WordTrace (prefixWord ++ tailWord_2175328) baseStart_2175328 baseEnd_2175328 := by
    simpa [prefixWord, tailWord_2175328, baseEnd_2175328] using wordTrace_append hprefix tailTrace_2175328
  have hstable : (prefixWord ++ tailWord_2175328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175328).length < 2 ^ (prefixWord ++ tailWord_2175328).sum := by decide
  have hdescent : baseEnd_2175328 < baseStart_2175328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175344 : List Nat := [2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 4]
def baseStart_2175344 : Nat := 118140960795 + 2175344 * 2 ^ 59
def prefixEnd_2175344 : Nat := 4983230072969 + 3 ^ 40 * 2175344 * 2
def baseEnd_2175344 : Nat := 1116997060874242190295781

theorem tailTrace_2175344 : CollatzResearch.WordTrace tailWord_2175344 prefixEnd_2175344 1116997060874242190295781 := by
  unfold tailWord_2175344
  simp only [CollatzResearch.WordTrace]
  refine ⟨39670656915553841011078543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52894209220738454681438057 39670656915553841011078543)
  ·
    refine ⟨59505985373330761516617815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39670656915553841011078543 59505985373330761516617815)
    ·
      refine ⟨89258978059996142274926723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59505985373330761516617815 89258978059996142274926723)
      ·
        refine ⟨133888467089994213412390085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89258978059996142274926723 133888467089994213412390085)
        ·
          refine ⟨25104087579373915014823141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 133888467089994213412390085 25104087579373915014823141)
          ·
            refine ⟨4707016421132609065279339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25104087579373915014823141 4707016421132609065279339)
            ·
              refine ⟨7060524631698913597919009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4707016421132609065279339 7060524631698913597919009)
              ·
                refine ⟨5295393473774185198439257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7060524631698913597919009 5295393473774185198439257)
                ·
                  refine ⟨3971545105330638898829443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5295393473774185198439257 3971545105330638898829443)
                  ·
                    refine ⟨5957317657995958348244165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3971545105330638898829443 5957317657995958348244165)
                    ·
                      refine ⟨1116997060874242190295781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5957317657995958348244165 1116997060874242190295781)
                      ·
                        rfl

theorem cell23_2175344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 4].length) (baseStart_2175344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2175344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2175344 prefixEnd_2175344 := by exact prefixLift 2175344
  have htrace : WordTrace (prefixWord ++ tailWord_2175344) baseStart_2175344 baseEnd_2175344 := by
    simpa [prefixWord, tailWord_2175344, baseEnd_2175344] using wordTrace_append hprefix tailTrace_2175344
  have hstable : (prefixWord ++ tailWord_2175344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175344).length < 2 ^ (prefixWord ++ tailWord_2175344).sum := by decide
  have hdescent : baseEnd_2175344 < baseStart_2175344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175364 : List Nat := [2, 3, 2, 1, 1, 2, 1, 2, 4, 2, 3]
def baseStart_2175364 : Nat := 118140960795 + 2175364 * 2 ^ 59
def prefixEnd_2175364 : Nat := 4983230072969 + 3 ^ 40 * 2175364 * 2
def baseEnd_2175364 : Nat := 1117007330487332112045689

theorem tailTrace_2175364 : CollatzResearch.WordTrace tailWord_2175364 prefixEnd_2175364 1117007330487332112045689 := by
  unfold tailWord_2175364
  simp only [CollatzResearch.WordTrace]
  refine ⟨39671021645517612718942573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52894695527356816958590097 39671021645517612718942573)
  ·
    refine ⟨14876633117069104769603465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39671021645517612718942573 14876633117069104769603465)
    ·
      refine ⟨11157474837801828577202599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14876633117069104769603465 11157474837801828577202599)
      ·
        refine ⟨16736212256702742865803899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11157474837801828577202599 16736212256702742865803899)
        ·
          refine ⟨25104318385054114298705849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16736212256702742865803899 25104318385054114298705849)
          ·
            refine ⟨18828238788790585724029387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25104318385054114298705849 18828238788790585724029387)
            ·
              refine ⟨28242358183185878586044081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18828238788790585724029387 28242358183185878586044081)
              ·
                refine ⟨21181768637389408939533061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28242358183185878586044081 21181768637389408939533061)
                ·
                  refine ⟨3971581619510514176162449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21181768637389408939533061 3971581619510514176162449)
                  ·
                    refine ⟨2978686214632885632121837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3971581619510514176162449 2978686214632885632121837)
                    ·
                      refine ⟨1117007330487332112045689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2978686214632885632121837 1117007330487332112045689)
                      ·
                        rfl

theorem cell23_2175364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_2175364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2175364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2175364 prefixEnd_2175364 := by exact prefixLift 2175364
  have htrace : WordTrace (prefixWord ++ tailWord_2175364) baseStart_2175364 baseEnd_2175364 := by
    simpa [prefixWord, tailWord_2175364, baseEnd_2175364] using wordTrace_append hprefix tailTrace_2175364
  have hstable : (prefixWord ++ tailWord_2175364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175364).length < 2 ^ (prefixWord ++ tailWord_2175364).sum := by decide
  have hdescent : baseEnd_2175364 < baseStart_2175364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175404 : List Nat := [2, 2, 1, 1, 1, 1, 3, 2, 3, 5, 2]
def baseStart_2175404 : Nat := 118140960795 + 2175404 * 2 ^ 59
def prefixEnd_2175404 : Nat := 4983230072969 + 3 ^ 40 * 2175404 * 2
def baseEnd_2175404 : Nat := 1117027869713511955545505

theorem tailTrace_2175404 : CollatzResearch.WordTrace tailWord_2175404 prefixEnd_2175404 1117027869713511955545505 := by
  unfold tailWord_2175404
  simp only [CollatzResearch.WordTrace]
  refine ⟨39671751105445156134670633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52895668140593541512894177 39671751105445156134670633)
  ·
    refine ⟨29753813329083867101002975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39671751105445156134670633 29753813329083867101002975)
    ·
      refine ⟨44630719993625800651504463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29753813329083867101002975 44630719993625800651504463)
      ·
        refine ⟨66946079990438700977256695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44630719993625800651504463 66946079990438700977256695)
        ·
          refine ⟨100419119985658051465885043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66946079990438700977256695 100419119985658051465885043)
          ·
            refine ⟨150628679978487077198827565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100419119985658051465885043 150628679978487077198827565)
            ·
              refine ⟨56485754991932653949560337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 150628679978487077198827565 56485754991932653949560337)
              ·
                refine ⟨42364316243949490462170253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56485754991932653949560337 42364316243949490462170253)
                ·
                  refine ⟨15886618591481058923313845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42364316243949490462170253 15886618591481058923313845)
                  ·
                    refine ⟨1489370492951349274060673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15886618591481058923313845 1489370492951349274060673)
                    ·
                      refine ⟨1117027869713511955545505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1489370492951349274060673 1117027869713511955545505)
                      ·
                        rfl

theorem cell23_2175404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 5, 2].length) (baseStart_2175404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2175404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2175404 prefixEnd_2175404 := by exact prefixLift 2175404
  have htrace : WordTrace (prefixWord ++ tailWord_2175404) baseStart_2175404 baseEnd_2175404 := by
    simpa [prefixWord, tailWord_2175404, baseEnd_2175404] using wordTrace_append hprefix tailTrace_2175404
  have hstable : (prefixWord ++ tailWord_2175404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175404).length < 2 ^ (prefixWord ++ tailWord_2175404).sum := by decide
  have hdescent : baseEnd_2175404 < baseStart_2175404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175405 : List Nat := [1, 5, 2, 2, 2, 1, 1, 4, 1, 4]
def baseStart_2175405 : Nat := 118140960795 + 2175405 * 2 ^ 59
def prefixEnd_2175405 : Nat := 4983230072969 + 3 ^ 40 * 2175405 * 2
def baseEnd_2175405 : Nat := 372342794398055483877667

theorem tailTrace_2175405 : CollatzResearch.WordTrace tailWord_2175405 prefixEnd_2175405 372342794398055483877667 := by
  unfold tailWord_2175405
  simp only [CollatzResearch.WordTrace]
  refine ⟨79343538683886689440127669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52895692455924459626751779 79343538683886689440127669)
  ·
    refine ⟨7438456751614377135011969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 79343538683886689440127669 7438456751614377135011969)
    ·
      refine ⟨5578842563710782851258977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7438456751614377135011969 5578842563710782851258977)
      ·
        refine ⟨4184131922783087138444233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5578842563710782851258977 4184131922783087138444233)
        ·
          refine ⟨3138098942087315353833175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4184131922783087138444233 3138098942087315353833175)
          ·
            refine ⟨4707148413130973030749763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3138098942087315353833175 4707148413130973030749763)
            ·
              refine ⟨7060722619696459546124645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4707148413130973030749763 7060722619696459546124645)
              ·
                refine ⟨1323885491193086164898371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7060722619696459546124645 1323885491193086164898371)
                ·
                  refine ⟨1985828236789629247347557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1323885491193086164898371 1985828236789629247347557)
                  ·
                    refine ⟨372342794398055483877667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1985828236789629247347557 372342794398055483877667)
                    ·
                      rfl

theorem cell23_2175405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_2175405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2175405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2175405 prefixEnd_2175405 := by exact prefixLift 2175405
  have htrace : WordTrace (prefixWord ++ tailWord_2175405) baseStart_2175405 baseEnd_2175405 := by
    simpa [prefixWord, tailWord_2175405, baseEnd_2175405] using wordTrace_append hprefix tailTrace_2175405
  have hstable : (prefixWord ++ tailWord_2175405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175405).length < 2 ^ (prefixWord ++ tailWord_2175405).sum := by decide
  have hdescent : baseEnd_2175405 < baseStart_2175405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175434 : List Nat := [3, 1, 2, 1, 2, 2, 1, 3, 3, 1, 4]
def baseStart_2175434 : Nat := 118140960795 + 2175434 * 2 ^ 59
def prefixEnd_2175434 : Nat := 4983230072969 + 3 ^ 40 * 2175434 * 2
def baseEnd_2175434 : Nat := 1117043274133146838170367

theorem tailTrace_2175434 : CollatzResearch.WordTrace tailWord_2175434 prefixEnd_2175434 1117043274133146838170367 := by
  unfold tailWord_2175434
  simp only [CollatzResearch.WordTrace]
  refine ⟨19836149100195406848233339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52896397600521084928622237 19836149100195406848233339)
  ·
    refine ⟨29754223650293110272350009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19836149100195406848233339 29754223650293110272350009)
    ·
      refine ⟨22315667737719832704262507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29754223650293110272350009 22315667737719832704262507)
      ·
        refine ⟨33473501606579749056393761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22315667737719832704262507 33473501606579749056393761)
        ·
          refine ⟨25105126204934811792295321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33473501606579749056393761 25105126204934811792295321)
          ·
            refine ⟨18828844653701108844221491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25105126204934811792295321 18828844653701108844221491)
            ·
              refine ⟨28243266980551663266332237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18828844653701108844221491 28243266980551663266332237)
              ·
                refine ⟨10591225117706873724874589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28243266980551663266332237 10591225117706873724874589)
                ·
                  refine ⟨3971709419140077646827971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10591225117706873724874589 3971709419140077646827971)
                  ·
                    refine ⟨5957564128710116470241957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3971709419140077646827971 5957564128710116470241957)
                    ·
                      refine ⟨1117043274133146838170367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5957564128710116470241957 1117043274133146838170367)
                      ·
                        rfl

theorem cell23_2175434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 3, 1, 4].length) (baseStart_2175434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2175434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2175434 prefixEnd_2175434 := by exact prefixLift 2175434
  have htrace : WordTrace (prefixWord ++ tailWord_2175434) baseStart_2175434 baseEnd_2175434 := by
    simpa [prefixWord, tailWord_2175434, baseEnd_2175434] using wordTrace_append hprefix tailTrace_2175434
  have hstable : (prefixWord ++ tailWord_2175434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175434).length < 2 ^ (prefixWord ++ tailWord_2175434).sum := by decide
  have hdescent : baseEnd_2175434 < baseStart_2175434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175445 : List Nat := [1, 3, 2, 3, 1, 3, 2, 3, 1, 1, 3]
def baseStart_2175445 : Nat := 118140960795 + 2175445 * 2 ^ 59
def prefixEnd_2175445 : Nat := 4983230072969 + 3 ^ 40 * 2175445 * 2
def baseEnd_2175445 : Nat := 1117048922420346295132817

theorem tailTrace_2175445 : CollatzResearch.WordTrace tailWord_2175445 prefixEnd_2175445 1117048922420346295132817 := by
  unfold tailWord_2175445
  simp only [CollatzResearch.WordTrace]
  refine ⟨79344997603741776271583789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52896665069161184181055859 79344997603741776271583789)
  ·
    refine ⟨29754374101403166101843921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79344997603741776271583789 29754374101403166101843921)
    ·
      refine ⟨22315780576052374576382941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29754374101403166101843921 22315780576052374576382941)
      ·
        refine ⟨8368417716019640466143603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22315780576052374576382941 8368417716019640466143603)
        ·
          refine ⟨12552626574029460699215405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8368417716019640466143603 12552626574029460699215405)
          ·
            refine ⟨4707234965261047762205777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12552626574029460699215405 4707234965261047762205777)
            ·
              refine ⟨3530426223945785821654333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4707234965261047762205777 3530426223945785821654333)
              ·
                refine ⟨1323909833979669683120375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3530426223945785821654333 1323909833979669683120375)
                ·
                  refine ⟨1985864750969504524680563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1323909833979669683120375 1985864750969504524680563)
                  ·
                    refine ⟨2978797126454256787020845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1985864750969504524680563 2978797126454256787020845)
                    ·
                      refine ⟨1117048922420346295132817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2978797126454256787020845 1117048922420346295132817)
                      ·
                        rfl

theorem cell23_2175445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_2175445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2175445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2175445 prefixEnd_2175445 := by exact prefixLift 2175445
  have htrace : WordTrace (prefixWord ++ tailWord_2175445) baseStart_2175445 baseEnd_2175445 := by
    simpa [prefixWord, tailWord_2175445, baseEnd_2175445] using wordTrace_append hprefix tailTrace_2175445
  have hstable : (prefixWord ++ tailWord_2175445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175445).length < 2 ^ (prefixWord ++ tailWord_2175445).sum := by decide
  have hdescent : baseEnd_2175445 < baseStart_2175445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175447 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 6]
def baseStart_2175447 : Nat := 118140960795 + 2175447 * 2 ^ 59
def prefixEnd_2175447 : Nat := 4983230072969 + 3 ^ 40 * 2175447 * 2
def baseEnd_2175447 : Nat := 1117049949381655287307807

theorem tailTrace_2175447 : CollatzResearch.WordTrace tailWord_2175447 prefixEnd_2175447 1117049949381655287307807 := by
  unfold tailWord_2175447
  simp only [CollatzResearch.WordTrace]
  refine ⟨79345070549734530613156595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52896713699823020408771063 79345070549734530613156595)
  ·
    refine ⟨119017605824601795919734893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79345070549734530613156595 119017605824601795919734893)
    ·
      refine ⟨44631602184225673469900585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119017605824601795919734893 44631602184225673469900585)
      ·
        refine ⟨33473701638169255102425439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44631602184225673469900585 33473701638169255102425439)
        ·
          refine ⟨50210552457253882653638159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33473701638169255102425439 50210552457253882653638159)
          ·
            refine ⟨75315828685880823980457239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50210552457253882653638159 75315828685880823980457239)
            ·
              refine ⟨112973743028821235970685859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75315828685880823980457239 112973743028821235970685859)
              ·
                refine ⟨169460614543231853956028789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112973743028821235970685859 169460614543231853956028789)
                ·
                  refine ⟨15886932613427986308377699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 169460614543231853956028789 15886932613427986308377699)
                  ·
                    refine ⟨23830398920141979462566549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15886932613427986308377699 23830398920141979462566549)
                    ·
                      refine ⟨1117049949381655287307807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23830398920141979462566549 1117049949381655287307807)
                      ·
                        rfl

theorem cell23_2175447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_2175447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2175447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2175447 prefixEnd_2175447 := by exact prefixLift 2175447
  have htrace : WordTrace (prefixWord ++ tailWord_2175447) baseStart_2175447 baseEnd_2175447 := by
    simpa [prefixWord, tailWord_2175447, baseEnd_2175447] using wordTrace_append hprefix tailTrace_2175447
  have hstable : (prefixWord ++ tailWord_2175447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175447).length < 2 ^ (prefixWord ++ tailWord_2175447).sum := by decide
  have hdescent : baseEnd_2175447 < baseStart_2175447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175457 : List Nat := [1, 2, 3, 1, 2, 2, 12]
def baseStart_2175457 : Nat := 118140960795 + 2175457 * 2 ^ 59
def prefixEnd_2175457 : Nat := 4983230072969 + 3 ^ 40 * 2175457 * 2
def baseEnd_2175457 : Nat := 13790803508496299360281

theorem tailTrace_2175457 : CollatzResearch.WordTrace tailWord_2175457 prefixEnd_2175457 13790803508496299360281 := by
  unfold tailWord_2175457
  simp only [CollatzResearch.WordTrace]
  refine ⟨79345435279698302321020625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52896956853132201547347083 79345435279698302321020625)
  ·
    refine ⟨59509076459773726740765469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79345435279698302321020625 59509076459773726740765469)
    ·
      refine ⟨22315903672415147527787051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59509076459773726740765469 22315903672415147527787051)
      ·
        refine ⟨33473855508622721291680577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22315903672415147527787051 33473855508622721291680577)
        ·
          refine ⟨25105391631467040968760433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33473855508622721291680577 25105391631467040968760433)
          ·
            refine ⟨18829043723600280726570325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25105391631467040968760433 18829043723600280726570325)
            ·
              refine ⟨13790803508496299360281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 18829043723600280726570325 13790803508496299360281)
              ·
                rfl

theorem cell23_2175457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 12].length) (baseStart_2175457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2175457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2175457 prefixEnd_2175457 := by exact prefixLift 2175457
  have htrace : WordTrace (prefixWord ++ tailWord_2175457) baseStart_2175457 baseEnd_2175457 := by
    simpa [prefixWord, tailWord_2175457, baseEnd_2175457] using wordTrace_append hprefix tailTrace_2175457
  have hstable : (prefixWord ++ tailWord_2175457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175457).length < 2 ^ (prefixWord ++ tailWord_2175457).sum := by decide
  have hdescent : baseEnd_2175457 < baseStart_2175457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175468 : List Nat := [2, 2, 1, 1, 2, 1, 6, 1, 3, 2, 2]
def baseStart_2175468 : Nat := 118140960795 + 2175468 * 2 ^ 59
def prefixEnd_2175468 : Nat := 4983230072969 + 3 ^ 40 * 2175468 * 2
def baseEnd_2175468 : Nat := 1117060732475399705145211

theorem tailTrace_2175468 : CollatzResearch.WordTrace tailWord_2175468 prefixEnd_2175468 1117060732475399705145211 := by
  unfold tailWord_2175468
  simp only [CollatzResearch.WordTrace]
  refine ⟨39672918241329225599835529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52897224321772300799780705 39672918241329225599835529)
  ·
    refine ⟨29754688680996919199876647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39672918241329225599835529 29754688680996919199876647)
    ·
      refine ⟨44632033021495378799814971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29754688680996919199876647 44632033021495378799814971)
      ·
        refine ⟨66948049532243068199722457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44632033021495378799814971 66948049532243068199722457)
        ·
          refine ⟨50211037149182301149791843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66948049532243068199722457 50211037149182301149791843)
          ·
            refine ⟨75316555723773451724687765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50211037149182301149791843 75316555723773451724687765)
            ·
              refine ⟨3530463549551880549594739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 75316555723773451724687765 3530463549551880549594739)
              ·
                refine ⟨5295695324327820824392109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3530463549551880549594739 5295695324327820824392109)
                ·
                  refine ⟨1985885746622932809147041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5295695324327820824392109 1985885746622932809147041)
                  ·
                    refine ⟨1489414309967199606860281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1985885746622932809147041 1489414309967199606860281)
                    ·
                      refine ⟨1117060732475399705145211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1489414309967199606860281 1117060732475399705145211)
                      ·
                        rfl

theorem cell23_2175468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 2, 2].length) (baseStart_2175468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2175468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2175468 prefixEnd_2175468 := by exact prefixLift 2175468
  have htrace : WordTrace (prefixWord ++ tailWord_2175468) baseStart_2175468 baseEnd_2175468 := by
    simpa [prefixWord, tailWord_2175468, baseEnd_2175468] using wordTrace_append hprefix tailTrace_2175468
  have hstable : (prefixWord ++ tailWord_2175468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175468).length < 2 ^ (prefixWord ++ tailWord_2175468).sum := by decide
  have hdescent : baseEnd_2175468 < baseStart_2175468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175502 : List Nat := [4, 1, 1, 2, 3, 1, 3, 3, 1, 2, 2]
def baseStart_2175502 : Nat := 118140960795 + 2175502 * 2 ^ 59
def prefixEnd_2175502 : Nat := 4983230072969 + 3 ^ 40 * 2175502 * 2
def baseEnd_2175502 : Nat := 1117078190817652572120055

theorem tailTrace_2175502 : CollatzResearch.WordTrace tailWord_2175502 prefixEnd_2175502 1117078190817652572120055 := by
  unfold tailWord_2175502
  simp only [CollatzResearch.WordTrace]
  refine ⟨9918384570566909375801095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52898051043023516670939173 9918384570566909375801095)
  ·
    refine ⟨14877576855850364063701643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9918384570566909375801095 14877576855850364063701643)
    ·
      refine ⟨22316365283775546095552465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14877576855850364063701643 22316365283775546095552465)
      ·
        refine ⟨16737273962831659571664349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22316365283775546095552465 16737273962831659571664349)
        ·
          refine ⟨6276477736061872339374131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16737273962831659571664349 6276477736061872339374131)
          ·
            refine ⟨9414716604092808509061197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6276477736061872339374131 9414716604092808509061197)
            ·
              refine ⟨3530518726534803190897949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9414716604092808509061197 3530518726534803190897949)
              ·
                refine ⟨1323944522450551196586731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3530518726534803190897949 1323944522450551196586731)
                ·
                  refine ⟨1985916783675826794880097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1323944522450551196586731 1985916783675826794880097)
                  ·
                    refine ⟨1489437587756870096160073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1985916783675826794880097 1489437587756870096160073)
                    ·
                      refine ⟨1117078190817652572120055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1489437587756870096160073 1117078190817652572120055)
                      ·
                        rfl

theorem cell23_2175502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 3, 1, 2, 2].length) (baseStart_2175502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2175502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2175502 prefixEnd_2175502 := by exact prefixLift 2175502
  have htrace : WordTrace (prefixWord ++ tailWord_2175502) baseStart_2175502 baseEnd_2175502 := by
    simpa [prefixWord, tailWord_2175502, baseEnd_2175502] using wordTrace_append hprefix tailTrace_2175502
  have hstable : (prefixWord ++ tailWord_2175502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175502).length < 2 ^ (prefixWord ++ tailWord_2175502).sum := by decide
  have hdescent : baseEnd_2175502 < baseStart_2175502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175544 : List Nat := [2, 1, 2, 1, 4, 1, 1, 1, 4, 1, 5]
def baseStart_2175544 : Nat := 118140960795 + 2175544 * 2 ^ 59
def prefixEnd_2175544 : Nat := 4983230072969 + 3 ^ 40 * 2175544 * 2
def baseEnd_2175544 : Nat := 1117099757005141407794861

theorem tailTrace_2175544 : CollatzResearch.WordTrace tailWord_2175544 prefixEnd_2175544 1117099757005141407794861 := by
  unfold tailWord_2175544
  simp only [CollatzResearch.WordTrace]
  refine ⟨39674304215191558089718843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52899072286922077452958457 39674304215191558089718843)
  ·
    refine ⟨59511456322787337134578265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39674304215191558089718843 59511456322787337134578265)
    ·
      refine ⟨44633592242090502850933699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59511456322787337134578265 44633592242090502850933699)
      ·
        refine ⟨66950388363135754276400549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44633592242090502850933699 66950388363135754276400549)
        ·
          refine ⟨12553197818087953926825103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66950388363135754276400549 12553197818087953926825103)
          ·
            refine ⟨18829796727131930890237655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12553197818087953926825103 18829796727131930890237655)
            ·
              refine ⟨28244695090697896335356483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18829796727131930890237655 28244695090697896335356483)
              ·
                refine ⟨42367042636046844503034725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28244695090697896335356483 42367042636046844503034725)
                ·
                  refine ⟨7943820494258783344319011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42367042636046844503034725 7943820494258783344319011)
                  ·
                    refine ⟨11915730741388175016478517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7943820494258783344319011 11915730741388175016478517)
                    ·
                      refine ⟨1117099757005141407794861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11915730741388175016478517 1117099757005141407794861)
                      ·
                        rfl

theorem cell23_2175544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 4, 1, 5].length) (baseStart_2175544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2175544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2175544 prefixEnd_2175544 := by exact prefixLift 2175544
  have htrace : WordTrace (prefixWord ++ tailWord_2175544) baseStart_2175544 baseEnd_2175544 := by
    simpa [prefixWord, tailWord_2175544, baseEnd_2175544] using wordTrace_append hprefix tailTrace_2175544
  have hstable : (prefixWord ++ tailWord_2175544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175544).length < 2 ^ (prefixWord ++ tailWord_2175544).sum := by decide
  have hdescent : baseEnd_2175544 < baseStart_2175544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175575 : List Nat := [1, 1, 3, 2, 2, 2, 4, 2, 2, 2, 2]
def baseStart_2175575 : Nat := 118140960795 + 2175575 * 2 ^ 59
def prefixEnd_2175575 : Nat := 4983230072969 + 3 ^ 40 * 2175575 * 2
def baseEnd_2175575 : Nat := 1117115674905430786507219

theorem tailTrace_2175575 : CollatzResearch.WordTrace tailWord_2175575 prefixEnd_2175575 1117115674905430786507219 := by
  unfold tailWord_2175575
  simp only [CollatzResearch.WordTrace]
  refine ⟨79349739093270808473816179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52899826062180538982544119 79349739093270808473816179)
  ·
    refine ⟨119024608639906212710724269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79349739093270808473816179 119024608639906212710724269)
    ·
      refine ⟨44634228239964829766521601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119024608639906212710724269 44634228239964829766521601)
      ·
        refine ⟨33475671179973622324891201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44634228239964829766521601 33475671179973622324891201)
        ·
          refine ⟨25106753384980216743668401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33475671179973622324891201 25106753384980216743668401)
          ·
            refine ⟨18830065038735162557751301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25106753384980216743668401 18830065038735162557751301)
            ·
              refine ⟨3530637194762842979578369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18830065038735162557751301 3530637194762842979578369)
              ·
                refine ⟨2647977896072132234683777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3530637194762842979578369 2647977896072132234683777)
                ·
                  refine ⟨1985983422054099176012833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2647977896072132234683777 1985983422054099176012833)
                  ·
                    refine ⟨1489487566540574382009625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1985983422054099176012833 1489487566540574382009625)
                    ·
                      refine ⟨1117115674905430786507219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1489487566540574382009625 1117115674905430786507219)
                      ·
                        rfl

theorem cell23_2175575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 2, 2, 2, 2].length) (baseStart_2175575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2175575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2175575 prefixEnd_2175575 := by exact prefixLift 2175575
  have htrace : WordTrace (prefixWord ++ tailWord_2175575) baseStart_2175575 baseEnd_2175575 := by
    simpa [prefixWord, tailWord_2175575, baseEnd_2175575] using wordTrace_append hprefix tailTrace_2175575
  have hstable : (prefixWord ++ tailWord_2175575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175575).length < 2 ^ (prefixWord ++ tailWord_2175575).sum := by decide
  have hdescent : baseEnd_2175575 < baseStart_2175575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175631 : List Nat := [1, 1, 2, 1, 1, 1, 1, 4, 3, 6, 2]
def baseStart_2175631 : Nat := 118140960795 + 2175631 * 2 ^ 59
def prefixEnd_2175631 : Nat := 4983230072969 + 3 ^ 40 * 2175631 * 2
def baseEnd_2175631 : Nat := 1117144429822082567406961

theorem tailTrace_2175631 : CollatzResearch.WordTrace tailWord_2175631 prefixEnd_2175631 1117144429822082567406961 := by
  unfold tailWord_2175631
  simp only [CollatzResearch.WordTrace]
  refine ⟨79351781581067930037854747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52901187720711953358569831 79351781581067930037854747)
  ·
    refine ⟨119027672371601895056782121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79351781581067930037854747 119027672371601895056782121)
    ·
      refine ⟨89270754278701421292586591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119027672371601895056782121 89270754278701421292586591)
      ·
        refine ⟨133906131418052131938879887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89270754278701421292586591 133906131418052131938879887)
        ·
          refine ⟨200859197127078197908319831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133906131418052131938879887 200859197127078197908319831)
          ·
            refine ⟨301288795690617296862479747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200859197127078197908319831 301288795690617296862479747)
            ·
              refine ⟨451933193535925945293719621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 301288795690617296862479747 451933193535925945293719621)
              ·
                refine ⟨84737473787986114742572429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 451933193535925945293719621 84737473787986114742572429)
                ·
                  refine ⟨31776552670494793028464661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 84737473787986114742572429 31776552670494793028464661)
                  ·
                    refine ⟨1489525906429443423209281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 31776552670494793028464661 1489525906429443423209281)
                    ·
                      refine ⟨1117144429822082567406961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1489525906429443423209281 1117144429822082567406961)
                      ·
                        rfl

theorem cell23_2175631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 6, 2].length) (baseStart_2175631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2175631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2175631 prefixEnd_2175631 := by exact prefixLift 2175631
  have htrace : WordTrace (prefixWord ++ tailWord_2175631) baseStart_2175631 baseEnd_2175631 := by
    simpa [prefixWord, tailWord_2175631, baseEnd_2175631] using wordTrace_append hprefix tailTrace_2175631
  have hstable : (prefixWord ++ tailWord_2175631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175631).length < 2 ^ (prefixWord ++ tailWord_2175631).sum := by decide
  have hdescent : baseEnd_2175631 < baseStart_2175631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175651 : List Nat := [1, 1, 1, 4, 1, 1, 2, 1, 6, 2, 3]
def baseStart_2175651 : Nat := 118140960795 + 2175651 * 2 ^ 59
def prefixEnd_2175651 : Nat := 4983230072969 + 3 ^ 40 * 2175651 * 2
def baseEnd_2175651 : Nat := 1117154699435172489156869

theorem tailTrace_2175651 : CollatzResearch.WordTrace tailWord_2175651 prefixEnd_2175651 1117154699435172489156869 := by
  unfold tailWord_2175651
  simp only [CollatzResearch.WordTrace]
  refine ⟨79352511040995473453582807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52901674027330315635721871 79352511040995473453582807)
  ·
    refine ⟨119028766561493210180374211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79352511040995473453582807 119028766561493210180374211)
    ·
      refine ⟨178543149842239815270561317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119028766561493210180374211 178543149842239815270561317)
      ·
        refine ⟨33476840595419965363230247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 178543149842239815270561317 33476840595419965363230247)
        ·
          refine ⟨50215260893129948044845371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33476840595419965363230247 50215260893129948044845371)
          ·
            refine ⟨75322891339694922067268057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50215260893129948044845371 75322891339694922067268057)
            ·
              refine ⟨56492168504771191550451043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75322891339694922067268057 56492168504771191550451043)
              ·
                refine ⟨84738252757156787325676565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56492168504771191550451043 84738252757156787325676565)
                ·
                  refine ⟨3972105597991724405891089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 84738252757156787325676565 3972105597991724405891089)
                  ·
                    refine ⟨2979079198493793304418317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3972105597991724405891089 2979079198493793304418317)
                    ·
                      refine ⟨1117154699435172489156869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2979079198493793304418317 1117154699435172489156869)
                      ·
                        rfl

theorem cell23_2175651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 6, 2, 3].length) (baseStart_2175651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2175651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2175651 prefixEnd_2175651 := by exact prefixLift 2175651
  have htrace : WordTrace (prefixWord ++ tailWord_2175651) baseStart_2175651 baseEnd_2175651 := by
    simpa [prefixWord, tailWord_2175651, baseEnd_2175651] using wordTrace_append hprefix tailTrace_2175651
  have hstable : (prefixWord ++ tailWord_2175651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175651).length < 2 ^ (prefixWord ++ tailWord_2175651).sum := by decide
  have hdescent : baseEnd_2175651 < baseStart_2175651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175738 : List Nat := [3, 1, 1, 1, 1, 3, 2, 5, 1, 1, 4]
def baseStart_2175738 : Nat := 118140960795 + 2175738 * 2 ^ 59
def prefixEnd_2175738 : Nat := 4983230072969 + 3 ^ 40 * 2175738 * 2
def baseEnd_2175738 : Nat := 1117199372252113648768969

theorem tailTrace_2175738 : CollatzResearch.WordTrace tailWord_2175738 prefixEnd_2175738 1117199372252113648768969 := by
  unfold tailWord_2175738
  simp only [CollatzResearch.WordTrace]
  refine ⟨19838921047920071827999967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52903789461120191541333245 19838921047920071827999967)
  ·
    refine ⟨29758381571880107741999951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19838921047920071827999967 29758381571880107741999951)
    ·
      refine ⟨44637572357820161612999927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29758381571880107741999951 44637572357820161612999927)
      ·
        refine ⟨66956358536730242419499891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44637572357820161612999927 66956358536730242419499891)
        ·
          refine ⟨100434537805095363629249837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66956358536730242419499891 100434537805095363629249837)
          ·
            refine ⟨37662951676910761360968689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100434537805095363629249837 37662951676910761360968689)
            ·
              refine ⟨28247213757683071020726517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37662951676910761360968689 28247213757683071020726517)
              ·
                refine ⟨2648176289782787908193111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28247213757683071020726517 2648176289782787908193111)
                ·
                  refine ⟨3972264434674181862289667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2648176289782787908193111 3972264434674181862289667)
                  ·
                    refine ⟨5958396652011272793434501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3972264434674181862289667 5958396652011272793434501)
                    ·
                      refine ⟨1117199372252113648768969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5958396652011272793434501 1117199372252113648768969)
                      ·
                        rfl

theorem cell23_2175738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 5, 1, 1, 4].length) (baseStart_2175738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2175738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2175738 prefixEnd_2175738 := by exact prefixLift 2175738
  have htrace : WordTrace (prefixWord ++ tailWord_2175738) baseStart_2175738 baseEnd_2175738 := by
    simpa [prefixWord, tailWord_2175738, baseEnd_2175738] using wordTrace_append hprefix tailTrace_2175738
  have hstable : (prefixWord ++ tailWord_2175738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175738).length < 2 ^ (prefixWord ++ tailWord_2175738).sum := by decide
  have hdescent : baseEnd_2175738 < baseStart_2175738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175742 : List Nat := [4, 2, 2, 1, 2, 1, 2, 2, 2, 3, 2]
def baseStart_2175742 : Nat := 118140960795 + 2175742 * 2 ^ 59
def prefixEnd_2175742 : Nat := 4983230072969 + 3 ^ 40 * 2175742 * 2
def baseEnd_2175742 : Nat := 1117201426174731633118951

theorem tailTrace_2175742 : CollatzResearch.WordTrace tailWord_2175742 prefixEnd_2175742 1117201426174731633118951 := by
  unfold tailWord_2175742
  simp only [CollatzResearch.WordTrace]
  refine ⟨9919478760458224499393185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52903886722443863996763653 9919478760458224499393185)
  ·
    refine ⟨7439609070343668374544889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9919478760458224499393185 7439609070343668374544889)
    ·
      refine ⟨5579706802757751280908667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7439609070343668374544889 5579706802757751280908667)
      ·
        refine ⟨8369560204136626921363001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5579706802757751280908667 8369560204136626921363001)
        ·
          refine ⟨6277170153102470191022251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8369560204136626921363001 6277170153102470191022251)
          ·
            refine ⟨9415755229653705286533377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6277170153102470191022251 9415755229653705286533377)
            ·
              refine ⟨7061816422240278964900033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9415755229653705286533377 7061816422240278964900033)
              ·
                refine ⟨5296362316680209223675025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7061816422240278964900033 5296362316680209223675025)
                ·
                  refine ⟨3972271737510156917756269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5296362316680209223675025 3972271737510156917756269)
                  ·
                    refine ⟨1489601901566308844158601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3972271737510156917756269 1489601901566308844158601)
                    ·
                      refine ⟨1117201426174731633118951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1489601901566308844158601 1117201426174731633118951)
                      ·
                        rfl

theorem cell23_2175742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_2175742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2175742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2175742 prefixEnd_2175742 := by exact prefixLift 2175742
  have htrace : WordTrace (prefixWord ++ tailWord_2175742) baseStart_2175742 baseEnd_2175742 := by
    simpa [prefixWord, tailWord_2175742, baseEnd_2175742] using wordTrace_append hprefix tailTrace_2175742
  have hstable : (prefixWord ++ tailWord_2175742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175742).length < 2 ^ (prefixWord ++ tailWord_2175742).sum := by decide
  have hdescent : baseEnd_2175742 < baseStart_2175742 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175755 : List Nat := [1, 1, 1, 1, 5, 1, 1, 5, 3, 2, 2]
def baseStart_2175755 : Nat := 118140960795 + 2175755 * 2 ^ 59
def prefixEnd_2175755 : Nat := 4983230072969 + 3 ^ 40 * 2175755 * 2
def baseEnd_2175755 : Nat := 1117208101423240082256391

theorem tailTrace_2175755 : CollatzResearch.WordTrace tailWord_2175755 prefixEnd_2175755 1117208101423240082256391 := by
  unfold tailWord_2175755
  simp only [CollatzResearch.WordTrace]
  refine ⟨79356304232618699215368719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52904202821745799476912479 79356304232618699215368719)
  ·
    refine ⟨119034456348928048823053079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79356304232618699215368719 119034456348928048823053079)
    ·
      refine ⟨178551684523392073234579619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119034456348928048823053079 178551684523392073234579619)
      ·
        refine ⟨267827526785088109851869429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178551684523392073234579619 267827526785088109851869429)
        ·
          refine ⟨25108830636102010298612759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 267827526785088109851869429 25108830636102010298612759)
          ·
            refine ⟨37663245954153015447919139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25108830636102010298612759 37663245954153015447919139)
            ·
              refine ⟨56494868931229523171878709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37663245954153015447919139 56494868931229523171878709)
              ·
                refine ⟨5296393962302767797363629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56494868931229523171878709 5296393962302767797363629)
                ·
                  refine ⟨1986147735863537924011361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5296393962302767797363629 1986147735863537924011361)
                  ·
                    refine ⟨1489610801897653443008521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1986147735863537924011361 1489610801897653443008521)
                    ·
                      refine ⟨1117208101423240082256391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1489610801897653443008521 1117208101423240082256391)
                      ·
                        rfl

theorem cell23_2175755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5, 3, 2, 2].length) (baseStart_2175755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2175755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2175755 prefixEnd_2175755 := by exact prefixLift 2175755
  have htrace : WordTrace (prefixWord ++ tailWord_2175755) baseStart_2175755 baseEnd_2175755 := by
    simpa [prefixWord, tailWord_2175755, baseEnd_2175755] using wordTrace_append hprefix tailTrace_2175755
  have hstable : (prefixWord ++ tailWord_2175755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175755).length < 2 ^ (prefixWord ++ tailWord_2175755).sum := by decide
  have hdescent : baseEnd_2175755 < baseStart_2175755 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175761 : List Nat := [1, 2, 2, 1, 1, 3, 5, 8]
def baseStart_2175761 : Nat := 118140960795 + 2175761 * 2 ^ 59
def prefixEnd_2175761 : Nat := 4983230072969 + 3 ^ 40 * 2175761 * 2
def baseEnd_2175761 : Nat := 41378191937302483658569

theorem tailTrace_2175761 : CollatzResearch.WordTrace tailWord_2175761 prefixEnd_2175761 41378191937302483658569 := by
  unfold tailWord_2175761
  simp only [CollatzResearch.WordTrace]
  refine ⟨79356523070596962240087137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52904348713731308160058091 79356523070596962240087137)
  ·
    refine ⟨59517392302947721680065353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79356523070596962240087137 59517392302947721680065353)
    ·
      refine ⟨44638044227210791260049015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59517392302947721680065353 44638044227210791260049015)
      ·
        refine ⟨66957066340816186890073523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44638044227210791260049015 66957066340816186890073523)
        ·
          refine ⟨100435599511224280335110285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66957066340816186890073523 100435599511224280335110285)
          ·
            refine ⟨37663349816709105125666357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100435599511224280335110285 37663349816709105125666357)
            ·
              refine ⟨3530939045316478605531221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37663349816709105125666357 3530939045316478605531221)
              ·
                refine ⟨41378191937302483658569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3530939045316478605531221 41378191937302483658569)
                ·
                  rfl

theorem cell23_2175761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 8].length) (baseStart_2175761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2175761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2175761 prefixEnd_2175761 := by exact prefixLift 2175761
  have htrace : WordTrace (prefixWord ++ tailWord_2175761) baseStart_2175761 baseEnd_2175761 := by
    simpa [prefixWord, tailWord_2175761, baseEnd_2175761] using wordTrace_append hprefix tailTrace_2175761
  have hstable : (prefixWord ++ tailWord_2175761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175761).length < 2 ^ (prefixWord ++ tailWord_2175761).sum := by decide
  have hdescent : baseEnd_2175761 < baseStart_2175761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175772 : List Nat := [2, 2, 3, 1, 1, 4, 1, 2, 3, 2, 2]
def baseStart_2175772 : Nat := 118140960795 + 2175772 * 2 ^ 59
def prefixEnd_2175772 : Nat := 4983230072969 + 3 ^ 40 * 2175772 * 2
def baseEnd_2175772 : Nat := 1117216830594366515743813

theorem tailTrace_2175772 : CollatzResearch.WordTrace tailWord_2175772 prefixEnd_2175772 1117216830594366515743813 := by
  unfold tailWord_2175772
  simp only [CollatzResearch.WordTrace]
  refine ⟨39678462136778555559368785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52904616182371407412491713 39678462136778555559368785)
  ·
    refine ⟨29758846602583916669526589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39678462136778555559368785 29758846602583916669526589)
    ·
      refine ⟨11159567475968968751072471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29758846602583916669526589 11159567475968968751072471)
      ·
        refine ⟨16739351213953453126608707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11159567475968968751072471 16739351213953453126608707)
        ·
          refine ⟨25109026820930179689913061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16739351213953453126608707 25109026820930179689913061)
          ·
            refine ⟨4707942528924408691858699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25109026820930179689913061 4707942528924408691858699)
            ·
              refine ⟨7061913793386613037788049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4707942528924408691858699 7061913793386613037788049)
              ·
                refine ⟨5296435345039959778341037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7061913793386613037788049 5296435345039959778341037)
                ·
                  refine ⟨1986163254389984916877889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5296435345039959778341037 1986163254389984916877889)
                  ·
                    refine ⟨1489622440792488687658417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1986163254389984916877889 1489622440792488687658417)
                    ·
                      refine ⟨1117216830594366515743813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1489622440792488687658417 1117216830594366515743813)
                      ·
                        rfl

theorem cell23_2175772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 2, 3, 2, 2].length) (baseStart_2175772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2175772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2175772 prefixEnd_2175772 := by exact prefixLift 2175772
  have htrace : WordTrace (prefixWord ++ tailWord_2175772) baseStart_2175772 baseEnd_2175772 := by
    simpa [prefixWord, tailWord_2175772, baseEnd_2175772] using wordTrace_append hprefix tailTrace_2175772
  have hstable : (prefixWord ++ tailWord_2175772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175772).length < 2 ^ (prefixWord ++ tailWord_2175772).sum := by decide
  have hdescent : baseEnd_2175772 < baseStart_2175772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175786 : List Nat := [3, 1, 4, 3, 2, 1, 2, 1, 1, 5]
def baseStart_2175786 : Nat := 118140960795 + 2175786 * 2 ^ 59
def prefixEnd_2175786 : Nat := 4983230072969 + 3 ^ 40 * 2175786 * 2
def baseEnd_2175786 : Nat := 372408006441176486989583

theorem tailTrace_2175786 : CollatzResearch.WordTrace tailWord_2175786 prefixEnd_2175786 372408006441176486989583 := by
  unfold tailWord_2175786
  simp only [CollatzResearch.WordTrace]
  refine ⟨19839358723876597877436803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52904956597004261006498141 19839358723876597877436803)
  ·
    refine ⟨29759038085814896816155205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19839358723876597877436803 29759038085814896816155205)
    ·
      refine ⟨5579819641090293153029101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29759038085814896816155205 5579819641090293153029101)
      ·
        refine ⟨2092432365408859932385913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5579819641090293153029101 2092432365408859932385913)
        ·
          refine ⟨1569324274056644949289435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2092432365408859932385913 1569324274056644949289435)
          ·
            refine ⟨2353986411084967423934153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1569324274056644949289435 2353986411084967423934153)
            ·
              refine ⟨1765489808313725567950615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2353986411084967423934153 1765489808313725567950615)
              ·
                refine ⟨2648234712470588351925923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1765489808313725567950615 2648234712470588351925923)
                ·
                  refine ⟨3972352068705882527888885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2648234712470588351925923 3972352068705882527888885)
                  ·
                    refine ⟨372408006441176486989583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3972352068705882527888885 372408006441176486989583)
                    ·
                      rfl

theorem cell23_2175786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_2175786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2175786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2175786 prefixEnd_2175786 := by exact prefixLift 2175786
  have htrace : WordTrace (prefixWord ++ tailWord_2175786) baseStart_2175786 baseEnd_2175786 := by
    simpa [prefixWord, tailWord_2175786, baseEnd_2175786] using wordTrace_append hprefix tailTrace_2175786
  have hstable : (prefixWord ++ tailWord_2175786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175786).length < 2 ^ (prefixWord ++ tailWord_2175786).sum := by decide
  have hdescent : baseEnd_2175786 < baseStart_2175786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175788 : List Nat := [2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 3]
def baseStart_2175788 : Nat := 118140960795 + 2175788 * 2 ^ 59
def prefixEnd_2175788 : Nat := 4983230072969 + 3 ^ 40 * 2175788 * 2
def baseEnd_2175788 : Nat := 1117225046284838453143739

theorem tailTrace_2175788 : CollatzResearch.WordTrace tailWord_2175788 prefixEnd_2175788 1117225046284838453143739 := by
  unfold tailWord_2175788
  simp only [CollatzResearch.WordTrace]
  refine ⟨39678753920749572925660009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52905005227666097234213345 39678753920749572925660009)
  ·
    refine ⟨29759065440562179694245007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39678753920749572925660009 29759065440562179694245007)
    ·
      refine ⟨44638598160843269541367511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29759065440562179694245007 44638598160843269541367511)
      ·
        refine ⟨66957897241264904312051267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44638598160843269541367511 66957897241264904312051267)
        ·
          refine ⟨100436845861897356468076901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66957897241264904312051267 100436845861897356468076901)
          ·
            refine ⟨18831908599105754337764419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100436845861897356468076901 18831908599105754337764419)
            ·
              refine ⟨28247862898658631506646629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18831908599105754337764419 28247862898658631506646629)
              ·
                refine ⟨5296474293498493407496243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28247862898658631506646629 5296474293498493407496243)
                ·
                  refine ⟨7944711440247740111244365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5296474293498493407496243 7944711440247740111244365)
                  ·
                    refine ⟨2979266790092902541716637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7944711440247740111244365 2979266790092902541716637)
                    ·
                      refine ⟨1117225046284838453143739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2979266790092902541716637 1117225046284838453143739)
                      ·
                        rfl

theorem cell23_2175788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 3].length) (baseStart_2175788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2175788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2175788 prefixEnd_2175788 := by exact prefixLift 2175788
  have htrace : WordTrace (prefixWord ++ tailWord_2175788) baseStart_2175788 baseEnd_2175788 := by
    simpa [prefixWord, tailWord_2175788, baseEnd_2175788] using wordTrace_append hprefix tailTrace_2175788
  have hstable : (prefixWord ++ tailWord_2175788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175788).length < 2 ^ (prefixWord ++ tailWord_2175788).sum := by decide
  have hdescent : baseEnd_2175788 < baseStart_2175788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175789 : List Nat := [1, 5, 3, 2, 1, 1, 1, 3, 1, 1, 4]
def baseStart_2175789 : Nat := 118140960795 + 2175789 * 2 ^ 59
def prefixEnd_2175789 : Nat := 4983230072969 + 3 ^ 40 * 2175789 * 2
def baseEnd_2175789 : Nat := 1117225559765492949231235

theorem tailTrace_2175789 : CollatzResearch.WordTrace tailWord_2175789 prefixEnd_2175789 1117225559765492949231235 := by
  unfold tailWord_2175789
  simp only [CollatzResearch.WordTrace]
  refine ⟨79357544314495523022106421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52905029542997015348070947 79357544314495523022106421)
  ·
    refine ⟨7439769779483955283322477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 79357544314495523022106421 7439769779483955283322477)
    ·
      refine ⟨2789913667306483231245929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7439769779483955283322477 2789913667306483231245929)
      ·
        refine ⟨2092435250479862423434447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2789913667306483231245929 2092435250479862423434447)
        ·
          refine ⟨3138652875719793635151671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2092435250479862423434447 3138652875719793635151671)
          ·
            refine ⟨4707979313579690452727507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3138652875719793635151671 4707979313579690452727507)
            ·
              refine ⟨7061968970369535679091261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4707979313579690452727507 7061968970369535679091261)
              ·
                refine ⟨2648238363888575879659223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7061968970369535679091261 2648238363888575879659223)
                ·
                  refine ⟨3972357545832863819488835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2648238363888575879659223 3972357545832863819488835)
                  ·
                    refine ⟨5958536318749295729233253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3972357545832863819488835 5958536318749295729233253)
                    ·
                      refine ⟨1117225559765492949231235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5958536318749295729233253 1117225559765492949231235)
                      ·
                        rfl

theorem cell23_2175789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_2175789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2175789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2175789 prefixEnd_2175789 := by exact prefixLift 2175789
  have htrace : WordTrace (prefixWord ++ tailWord_2175789) baseStart_2175789 baseEnd_2175789 := by
    simpa [prefixWord, tailWord_2175789, baseEnd_2175789] using wordTrace_append hprefix tailTrace_2175789
  have hstable : (prefixWord ++ tailWord_2175789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175789).length < 2 ^ (prefixWord ++ tailWord_2175789).sum := by decide
  have hdescent : baseEnd_2175789 < baseStart_2175789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175845 : List Nat := [1, 3, 1, 3, 1, 1, 2, 4, 1, 4, 2]
def baseStart_2175845 : Nat := 118140960795 + 2175845 * 2 ^ 59
def prefixEnd_2175845 : Nat := 4983230072969 + 3 ^ 40 * 2175845 * 2
def baseEnd_2175845 : Nat := 1117254314682144730130977

theorem tailTrace_2175845 : CollatzResearch.WordTrace tailWord_2175845 prefixEnd_2175845 1117254314682144730130977 := by
  unfold tailWord_2175845
  simp only [CollatzResearch.WordTrace]
  refine ⟨79359586802292644586144989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52906391201528429724096659 79359586802292644586144989)
  ·
    refine ⟨29759845050859741719804371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79359586802292644586144989 29759845050859741719804371)
    ·
      refine ⟨44639767576289612579706557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29759845050859741719804371 44639767576289612579706557)
      ·
        refine ⟨16739912841108604717389959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44639767576289612579706557 16739912841108604717389959)
        ·
          refine ⟨25109869261662907076084939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16739912841108604717389959 25109869261662907076084939)
          ·
            refine ⟨37664803892494360614127409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25109869261662907076084939 37664803892494360614127409)
            ·
              refine ⟨28248602919370770460595557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37664803892494360614127409 28248602919370770460595557)
              ·
                refine ⟨5296613047382019461361667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28248602919370770460595557 5296613047382019461361667)
                ·
                  refine ⟨7944919571073029192042501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5296613047382019461361667 7944919571073029192042501)
                  ·
                    refine ⟨1489672419576192973507969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7944919571073029192042501 1489672419576192973507969)
                    ·
                      refine ⟨1117254314682144730130977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1489672419576192973507969 1117254314682144730130977)
                      ·
                        rfl

theorem cell23_2175845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4, 1, 4, 2].length) (baseStart_2175845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2175845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2175845 prefixEnd_2175845 := by exact prefixLift 2175845
  have htrace : WordTrace (prefixWord ++ tailWord_2175845) baseStart_2175845 baseEnd_2175845 := by
    simpa [prefixWord, tailWord_2175845, baseEnd_2175845] using wordTrace_append hprefix tailTrace_2175845
  have hstable : (prefixWord ++ tailWord_2175845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175845).length < 2 ^ (prefixWord ++ tailWord_2175845).sum := by decide
  have hdescent : baseEnd_2175845 < baseStart_2175845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
