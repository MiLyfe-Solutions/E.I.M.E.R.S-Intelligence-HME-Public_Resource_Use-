import V185TrunkScan23Chunk0840

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4977405 : List Nat := [1, 4, 1, 1, 1, 1, 5, 2, 3, 4]
def baseStart_4977405 : Nat := 118140960795 + 4977405 * 2 ^ 59
def prefixEnd_4977405 : Nat := 4983230072969 + 3 ^ 40 * 4977405 * 2
def baseEnd_4977405 : Nat := 851933725697401204582279

theorem tailTrace_4977405 : CollatzResearch.WordTrace tailWord_4977405 prefixEnd_4977405 851933725697401204582279 := by
  unfold tailWord_4977405
  simp only [CollatzResearch.WordTrace]
  refine ⟨181540874532719232941333669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121027249688479488627555779 181540874532719232941333669)
  ·
    refine ⟨34038913974884856176500063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 181540874532719232941333669 34038913974884856176500063)
    ·
      refine ⟨51058370962327284264750095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34038913974884856176500063 51058370962327284264750095)
      ·
        refine ⟨76587556443490926397125143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51058370962327284264750095 76587556443490926397125143)
        ·
          refine ⟨114881334665236389595687715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76587556443490926397125143 114881334665236389595687715)
          ·
            refine ⟨172322001997854584393531573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114881334665236389595687715 172322001997854584393531573)
            ·
              refine ⟨16155187687298867286893585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 172322001997854584393531573 16155187687298867286893585)
              ·
                refine ⟨12116390765474150465170189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16155187687298867286893585 12116390765474150465170189)
                ·
                  refine ⟨4543646537052806424438821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12116390765474150465170189 4543646537052806424438821)
                  ·
                    refine ⟨851933725697401204582279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4543646537052806424438821 851933725697401204582279)
                    ·
                      rfl

theorem cell23_4977405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2, 3, 4].length) (baseStart_4977405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4977405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4977405 prefixEnd_4977405 := by exact prefixLift 4977405
  have htrace : WordTrace (prefixWord ++ tailWord_4977405) baseStart_4977405 baseEnd_4977405 := by
    simpa [prefixWord, tailWord_4977405, baseEnd_4977405] using wordTrace_append hprefix tailTrace_4977405
  have hstable : (prefixWord ++ tailWord_4977405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4977405).length < 2 ^ (prefixWord ++ tailWord_4977405).sum := by decide
  have hdescent : baseEnd_4977405 < baseStart_4977405 := by decide
  rcases family_descends (prefixWord ++ tailWord_4977405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4977418 : List Nat := [3, 1, 2, 2, 1, 2, 2, 2, 8]
def baseStart_4977418 : Nat := 118140960795 + 4977418 * 2 ^ 59
def prefixEnd_4977418 : Nat := 4983230072969 + 3 ^ 40 * 4977418 * 2
def baseEnd_4977418 : Nat := 283978650260079118098253

theorem tailTrace_4977418 : CollatzResearch.WordTrace tailWord_4977418 prefixEnd_4977418 283978650260079118098253 := by
  unfold tailWord_4977418
  simp only [CollatzResearch.WordTrace]
  refine ⟨45385337170418034040389227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121027565787781424107704605 45385337170418034040389227)
  ·
    refine ⟨68078005755627051060583841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45385337170418034040389227 68078005755627051060583841)
    ·
      refine ⟨51058504316720288295437881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68078005755627051060583841 51058504316720288295437881)
      ·
        refine ⟨38293878237540216221578411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51058504316720288295437881 38293878237540216221578411)
        ·
          refine ⟨57440817356310324332367617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38293878237540216221578411 57440817356310324332367617)
          ·
            refine ⟨43080613017232743249275713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57440817356310324332367617 43080613017232743249275713)
            ·
              refine ⟨32310459762924557436956785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43080613017232743249275713 32310459762924557436956785)
              ·
                refine ⟨24232844822193418077717589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32310459762924557436956785 24232844822193418077717589)
                ·
                  refine ⟨283978650260079118098253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24232844822193418077717589 283978650260079118098253)
                  ·
                    rfl

theorem cell23_4977418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 8].length) (baseStart_4977418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4977418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4977418 prefixEnd_4977418 := by exact prefixLift 4977418
  have htrace : WordTrace (prefixWord ++ tailWord_4977418) baseStart_4977418 baseEnd_4977418 := by
    simpa [prefixWord, tailWord_4977418, baseEnd_4977418] using wordTrace_append hprefix tailTrace_4977418
  have hstable : (prefixWord ++ tailWord_4977418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4977418).length < 2 ^ (prefixWord ++ tailWord_4977418).sum := by decide
  have hdescent : baseEnd_4977418 < baseStart_4977418 := by decide
  rcases family_descends (prefixWord ++ tailWord_4977418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4977473 : List Nat := [1, 2, 5, 3, 1, 2, 1, 3, 1, 4]
def baseStart_4977473 : Nat := 118140960795 + 4977473 * 2 ^ 59
def prefixEnd_4977473 : Nat := 4983230072969 + 3 ^ 40 * 4977473 * 2
def baseEnd_4977473 : Nat := 851945364592236449232175

theorem tailTrace_4977473 : CollatzResearch.WordTrace tailWord_4977473 prefixEnd_4977473 851945364592236449232175 := by
  unfold tailWord_4977473
  simp only [CollatzResearch.WordTrace]
  refine ⟨181543354696472880554809073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121028903130981920369872715 181543354696472880554809073)
  ·
    refine ⟨136157516022354660416106805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181543354696472880554809073 136157516022354660416106805)
    ·
      refine ⟨12764767127095749414010013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 136157516022354660416106805 12764767127095749414010013)
      ·
        refine ⟨4786787672660906030253755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12764767127095749414010013 4786787672660906030253755)
        ·
          refine ⟨7180181508991359045380633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4786787672660906030253755 7180181508991359045380633)
          ·
            refine ⟨5385136131743519284035475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7180181508991359045380633 5385136131743519284035475)
            ·
              refine ⟨8077704197615278926053213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5385136131743519284035475 8077704197615278926053213)
              ·
                refine ⟨3029139074105729597269955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8077704197615278926053213 3029139074105729597269955)
                ·
                  refine ⟨4543708611158594395904933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3029139074105729597269955 4543708611158594395904933)
                  ·
                    refine ⟨851945364592236449232175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4543708611158594395904933 851945364592236449232175)
                    ·
                      rfl

theorem cell23_4977473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_4977473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4977473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4977473 prefixEnd_4977473 := by exact prefixLift 4977473
  have htrace : WordTrace (prefixWord ++ tailWord_4977473) baseStart_4977473 baseEnd_4977473 := by
    simpa [prefixWord, tailWord_4977473, baseEnd_4977473] using wordTrace_append hprefix tailTrace_4977473
  have hstable : (prefixWord ++ tailWord_4977473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4977473).length < 2 ^ (prefixWord ++ tailWord_4977473).sum := by decide
  have hdescent : baseEnd_4977473 < baseStart_4977473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4977473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4977489 : List Nat := [1, 2, 2, 1, 6, 1, 1, 2, 2, 3, 2]
def baseStart_4977489 : Nat := 118140960795 + 4977489 * 2 ^ 59
def prefixEnd_4977489 : Nat := 4983230072969 + 3 ^ 40 * 4977489 * 2
def baseEnd_4977489 : Nat := 2555844309467181285096451

theorem tailTrace_4977489 : CollatzResearch.WordTrace tailWord_4977489 prefixEnd_4977489 2555844309467181285096451 := by
  unfold tailWord_4977489
  simp only [CollatzResearch.WordTrace]
  refine ⟨181543938264414915287391521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121029292176276610191594347 181543938264414915287391521)
  ·
    refine ⟨136157953698311186465543641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181543938264414915287391521 136157953698311186465543641)
    ·
      refine ⟨102118465273733389849157731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136157953698311186465543641 102118465273733389849157731)
      ·
        refine ⟨153177697910600084773736597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102118465273733389849157731 153177697910600084773736597)
        ·
          refine ⟨7180204589559378973768903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 153177697910600084773736597 7180204589559378973768903)
          ·
            refine ⟨10770306884339068460653355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7180204589559378973768903 10770306884339068460653355)
            ·
              refine ⟨16155460326508602690980033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10770306884339068460653355 16155460326508602690980033)
              ·
                refine ⟨12116595244881452018235025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16155460326508602690980033 12116595244881452018235025)
                ·
                  refine ⟨9087446433661089013676269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12116595244881452018235025 9087446433661089013676269)
                  ·
                    refine ⟨3407792412622908380128601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9087446433661089013676269 3407792412622908380128601)
                    ·
                      refine ⟨2555844309467181285096451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3407792412622908380128601 2555844309467181285096451)
                      ·
                        rfl

theorem cell23_4977489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 2, 2, 3, 2].length) (baseStart_4977489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4977489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4977489 prefixEnd_4977489 := by exact prefixLift 4977489
  have htrace : WordTrace (prefixWord ++ tailWord_4977489) baseStart_4977489 baseEnd_4977489 := by
    simpa [prefixWord, tailWord_4977489, baseEnd_4977489] using wordTrace_append hprefix tailTrace_4977489
  have hstable : (prefixWord ++ tailWord_4977489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4977489).length < 2 ^ (prefixWord ++ tailWord_4977489).sum := by decide
  have hdescent : baseEnd_4977489 < baseStart_4977489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4977489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4977525 : List Nat := [1, 3, 4, 1, 1, 2, 2, 9]
def baseStart_4977525 : Nat := 118140960795 + 4977525 * 2 ^ 59
def prefixEnd_4977525 : Nat := 4983230072969 + 3 ^ 40 * 4977525 * 2
def baseEnd_4977525 : Nat := 94661584991509005342455

theorem tailTrace_4977525 : CollatzResearch.WordTrace tailWord_4977525 prefixEnd_4977525 94661584991509005342455 := by
  unfold tailWord_4977525
  simp only [CollatzResearch.WordTrace]
  refine ⟨181545251292284493435702029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121030167528189662290468019 181545251292284493435702029)
  ·
    refine ⟨68079469234606685038388261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181545251292284493435702029 68079469234606685038388261)
    ·
      refine ⟨12764900481488753444697799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68079469234606685038388261 12764900481488753444697799)
      ·
        refine ⟨19147350722233130167046699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12764900481488753444697799 19147350722233130167046699)
        ·
          refine ⟨28721026083349695250570049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19147350722233130167046699 28721026083349695250570049)
          ·
            refine ⟨21540769562512271437927537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28721026083349695250570049 21540769562512271437927537)
            ·
              refine ⟨16155577171884203578445653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21540769562512271437927537 16155577171884203578445653)
              ·
                refine ⟨94661584991509005342455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16155577171884203578445653 94661584991509005342455)
                ·
                  rfl

theorem cell23_4977525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 9].length) (baseStart_4977525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4977525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4977525 prefixEnd_4977525 := by exact prefixLift 4977525
  have htrace : WordTrace (prefixWord ++ tailWord_4977525) baseStart_4977525 baseEnd_4977525 := by
    simpa [prefixWord, tailWord_4977525, baseEnd_4977525] using wordTrace_append hprefix tailTrace_4977525
  have hstable : (prefixWord ++ tailWord_4977525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4977525).length < 2 ^ (prefixWord ++ tailWord_4977525).sum := by decide
  have hdescent : baseEnd_4977525 < baseStart_4977525 := by decide
  rcases family_descends (prefixWord ++ tailWord_4977525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4977535 : List Nat := [1, 1, 2, 2, 1, 1, 5, 1, 3, 3, 3]
def baseStart_4977535 : Nat := 118140960795 + 4977535 * 2 ^ 59
def prefixEnd_4977535 : Nat := 4983230072969 + 3 ^ 40 * 4977535 * 2
def baseEnd_4977535 : Nat := 2555867929577288105121239

theorem tailTrace_4977535 : CollatzResearch.WordTrace tailWord_4977535 prefixEnd_4977535 2555867929577288105121239 := by
  unfold tailWord_4977535
  simp only [CollatzResearch.WordTrace]
  refine ⟨181545616022248265143566059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121030410681498843429044039 181545616022248265143566059)
  ·
    refine ⟨272318424033372397715349089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181545616022248265143566059 272318424033372397715349089)
    ·
      refine ⟨204238818025029298286511817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 272318424033372397715349089 204238818025029298286511817)
      ·
        refine ⟨153179113518771973714883863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204238818025029298286511817 153179113518771973714883863)
        ·
          refine ⟨229768670278157960572325795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153179113518771973714883863 229768670278157960572325795)
          ·
            refine ⟨344653005417236940858488693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229768670278157960572325795 344653005417236940858488693)
            ·
              refine ⟨32311219257865963205483315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 344653005417236940858488693 32311219257865963205483315)
              ·
                refine ⟨48466828886798944808224973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32311219257865963205483315 48466828886798944808224973)
                ·
                  refine ⟨18175060832549604303084365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48466828886798944808224973 18175060832549604303084365)
                  ·
                    refine ⟨6815647812206101613656637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18175060832549604303084365 6815647812206101613656637)
                    ·
                      refine ⟨2555867929577288105121239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6815647812206101613656637 2555867929577288105121239)
                      ·
                        rfl

theorem cell23_4977535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3, 3, 3].length) (baseStart_4977535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4977535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4977535 prefixEnd_4977535 := by exact prefixLift 4977535
  have htrace : WordTrace (prefixWord ++ tailWord_4977535) baseStart_4977535 baseEnd_4977535 := by
    simpa [prefixWord, tailWord_4977535, baseEnd_4977535] using wordTrace_append hprefix tailTrace_4977535
  have hstable : (prefixWord ++ tailWord_4977535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4977535).length < 2 ^ (prefixWord ++ tailWord_4977535).sum := by decide
  have hdescent : baseEnd_4977535 < baseStart_4977535 := by decide
  rcases family_descends (prefixWord ++ tailWord_4977535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4977539 : List Nat := [1, 1, 1, 3, 4, 1, 5, 1, 1, 2, 3]
def baseStart_4977539 : Nat := 118140960795 + 4977539 * 2 ^ 59
def prefixEnd_4977539 : Nat := 4983230072969 + 3 ^ 40 * 4977539 * 2
def baseEnd_4977539 : Nat := 2555869983499906089471221

theorem tailTrace_4977539 : CollatzResearch.WordTrace tailWord_4977539 prefixEnd_4977539 2555869983499906089471221 := by
  unfold tailWord_4977539
  simp only [CollatzResearch.WordTrace]
  refine ⟨181545761914233773826711671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121030507942822515884474447 181545761914233773826711671)
  ·
    refine ⟨272318642871350660740067507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181545761914233773826711671 272318642871350660740067507)
    ·
      refine ⟨408477964307025991110101261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272318642871350660740067507 408477964307025991110101261)
      ·
        refine ⟨153179236615134746666287973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 408477964307025991110101261 153179236615134746666287973)
        ·
          refine ⟨28721106865337764999928995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 153179236615134746666287973 28721106865337764999928995)
          ·
            refine ⟨43081660298006647499893493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28721106865337764999928995 43081660298006647499893493)
            ·
              refine ⟨4038905652938123203115015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43081660298006647499893493 4038905652938123203115015)
              ·
                refine ⟨6058358479407184804672523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4038905652938123203115015 6058358479407184804672523)
                ·
                  refine ⟨9087537719110777207008785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6058358479407184804672523 9087537719110777207008785)
                  ·
                    refine ⟨6815653289333082905256589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9087537719110777207008785 6815653289333082905256589)
                    ·
                      refine ⟨2555869983499906089471221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6815653289333082905256589 2555869983499906089471221)
                      ·
                        rfl

theorem cell23_4977539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 1, 1, 2, 3].length) (baseStart_4977539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4977539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4977539 prefixEnd_4977539 := by exact prefixLift 4977539
  have htrace : WordTrace (prefixWord ++ tailWord_4977539) baseStart_4977539 baseEnd_4977539 := by
    simpa [prefixWord, tailWord_4977539, baseEnd_4977539] using wordTrace_append hprefix tailTrace_4977539
  have hstable : (prefixWord ++ tailWord_4977539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4977539).length < 2 ^ (prefixWord ++ tailWord_4977539).sum := by decide
  have hdescent : baseEnd_4977539 < baseStart_4977539 := by decide
  rcases family_descends (prefixWord ++ tailWord_4977539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4977569 : List Nat := [1, 2, 3, 4, 1, 2, 2, 1, 1, 3, 3]
def baseStart_4977569 : Nat := 118140960795 + 4977569 * 2 ^ 59
def prefixEnd_4977569 : Nat := 4983230072969 + 3 ^ 40 * 4977569 * 2
def baseEnd_4977569 : Nat := 2555885387919540972096083

theorem tailTrace_4977569 : CollatzResearch.WordTrace tailWord_4977569 prefixEnd_4977569 2555885387919540972096083 := by
  unfold tailWord_4977569
  simp only [CollatzResearch.WordTrace]
  refine ⟨181546856104125088950303761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121031237402750059300202507 181546856104125088950303761)
  ·
    refine ⟨136160142078093816712727821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181546856104125088950303761 136160142078093816712727821)
    ·
      refine ⟨51060053279285181267272933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136160142078093816712727821 51060053279285181267272933)
      ·
        refine ⟨9573759989865971487613675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51060053279285181267272933 9573759989865971487613675)
        ·
          refine ⟨14360639984798957231420513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9573759989865971487613675 14360639984798957231420513)
          ·
            refine ⟨10770479988599217923565385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14360639984798957231420513 10770479988599217923565385)
            ·
              refine ⟨8077859991449413442674039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10770479988599217923565385 8077859991449413442674039)
              ·
                refine ⟨12116789987174120164011059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8077859991449413442674039 12116789987174120164011059)
                ·
                  refine ⟨18175184980761180246016589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12116789987174120164011059 18175184980761180246016589)
                  ·
                    refine ⟨6815694367785442592256221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18175184980761180246016589 6815694367785442592256221)
                    ·
                      refine ⟨2555885387919540972096083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6815694367785442592256221 2555885387919540972096083)
                      ·
                        rfl

theorem cell23_4977569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_4977569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4977569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4977569 prefixEnd_4977569 := by exact prefixLift 4977569
  have htrace : WordTrace (prefixWord ++ tailWord_4977569) baseStart_4977569 baseEnd_4977569 := by
    simpa [prefixWord, tailWord_4977569, baseEnd_4977569] using wordTrace_append hprefix tailTrace_4977569
  have hstable : (prefixWord ++ tailWord_4977569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4977569).length < 2 ^ (prefixWord ++ tailWord_4977569).sum := by decide
  have hdescent : baseEnd_4977569 < baseStart_4977569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4977569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4977590 : List Nat := [5, 1, 4, 1, 1, 1, 1, 3, 1, 2, 3]
def baseStart_4977590 : Nat := 118140960795 + 4977590 * 2 ^ 59
def prefixEnd_4977590 : Nat := 4983230072969 + 3 ^ 40 * 4977590 * 2
def baseEnd_4977590 : Nat := 2555896171013285389933487

theorem tailTrace_4977590 : CollatzResearch.WordTrace tailWord_4977590 prefixEnd_4977590 2555896171013285389933487 := by
  unfold tailWord_4977590
  simp only [CollatzResearch.WordTrace]
  refine ⟨11346726377315563096051139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 121031748024699339691212149 11346726377315563096051139)
  ·
    refine ⟨17020089565973344644076709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11346726377315563096051139 17020089565973344644076709)
    ·
      refine ⟨3191266793620002120764383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17020089565973344644076709 3191266793620002120764383)
      ·
        refine ⟨4786900190430003181146575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3191266793620002120764383 4786900190430003181146575)
        ·
          refine ⟨7180350285645004771719863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4786900190430003181146575 7180350285645004771719863)
          ·
            refine ⟨10770525428467507157579795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7180350285645004771719863 10770525428467507157579795)
            ·
              refine ⟨16155788142701260736369693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10770525428467507157579795 16155788142701260736369693)
              ·
                refine ⟨6058420553512972776138635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16155788142701260736369693 6058420553512972776138635)
                ·
                  refine ⟨9087630830269459164207953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6058420553512972776138635 9087630830269459164207953)
                  ·
                    refine ⟨6815723122702094373155965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9087630830269459164207953 6815723122702094373155965)
                    ·
                      refine ⟨2555896171013285389933487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6815723122702094373155965 2555896171013285389933487)
                      ·
                        rfl

theorem cell23_4977590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_4977590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4977590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4977590 prefixEnd_4977590 := by exact prefixLift 4977590
  have htrace : WordTrace (prefixWord ++ tailWord_4977590) baseStart_4977590 baseEnd_4977590 := by
    simpa [prefixWord, tailWord_4977590, baseEnd_4977590] using wordTrace_append hprefix tailTrace_4977590
  have hstable : (prefixWord ++ tailWord_4977590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4977590).length < 2 ^ (prefixWord ++ tailWord_4977590).sum := by decide
  have hdescent : baseEnd_4977590 < baseStart_4977590 := by decide
  rcases family_descends (prefixWord ++ tailWord_4977590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4977615 : List Nat := [1, 1, 2, 1, 1, 6, 1, 3, 7]
def baseStart_4977615 : Nat := 118140960795 + 4977615 * 2 ^ 59
def prefixEnd_4977615 : Nat := 4983230072969 + 3 ^ 40 * 4977615 * 2
def baseEnd_4977615 : Nat := 283989889781071976902319

theorem tailTrace_4977615 : CollatzResearch.WordTrace tailWord_4977615 prefixEnd_4977615 283989889781071976902319 := by
  unfold tailWord_4977615
  simp only [CollatzResearch.WordTrace]
  refine ⟨181548533861958438806478299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121032355907972292537652199 181548533861958438806478299)
  ·
    refine ⟨272322800792937658209717449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181548533861958438806478299 272322800792937658209717449)
    ·
      refine ⟨204242100594703243657288087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 272322800792937658209717449 204242100594703243657288087)
      ·
        refine ⟨306363150892054865485932131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204242100594703243657288087 306363150892054865485932131)
        ·
          refine ⟨459544726338082298228898197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 306363150892054865485932131 459544726338082298228898197)
          ·
            refine ⟨21541159047097607729479603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 459544726338082298228898197 21541159047097607729479603)
            ·
              refine ⟨32311738570646411594219405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21541159047097607729479603 32311738570646411594219405)
              ·
                refine ⟨12116901963992404347832277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32311738570646411594219405 12116901963992404347832277)
                ·
                  refine ⟨283989889781071976902319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12116901963992404347832277 283989889781071976902319)
                  ·
                    rfl

theorem cell23_4977615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3, 7].length) (baseStart_4977615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4977615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4977615 prefixEnd_4977615 := by exact prefixLift 4977615
  have htrace : WordTrace (prefixWord ++ tailWord_4977615) baseStart_4977615 baseEnd_4977615 := by
    simpa [prefixWord, tailWord_4977615, baseEnd_4977615] using wordTrace_append hprefix tailTrace_4977615
  have hstable : (prefixWord ++ tailWord_4977615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4977615).length < 2 ^ (prefixWord ++ tailWord_4977615).sum := by decide
  have hdescent : baseEnd_4977615 < baseStart_4977615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4977615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4977626 : List Nat := [3, 1, 1, 2, 4, 3, 1, 1, 1, 4, 2]
def baseStart_4977626 : Nat := 118140960795 + 4977626 * 2 ^ 59
def prefixEnd_4977626 : Nat := 4983230072969 + 3 ^ 40 * 4977626 * 2
def baseEnd_4977626 : Nat := 2555914656316847249083321

theorem tailTrace_4977626 : CollatzResearch.WordTrace tailWord_4977626 prefixEnd_4977626 2555914656316847249083321 := by
  unfold tailWord_4977626
  simp only [CollatzResearch.WordTrace]
  refine ⟨45387233766229646921282183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121032623376612391790085821 45387233766229646921282183)
  ·
    refine ⟨68080850649344470381923275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45387233766229646921282183 68080850649344470381923275)
    ·
      refine ⟨102121275974016705572884913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68080850649344470381923275 102121275974016705572884913)
      ·
        refine ⟨76590956980512529179663685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102121275974016705572884913 76590956980512529179663685)
        ·
          refine ⟨14360804433846099221186941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76590956980512529179663685 14360804433846099221186941)
          ·
            refine ⟨5385301662692287207945103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14360804433846099221186941 5385301662692287207945103)
            ·
              refine ⟨8077952494038430811917655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5385301662692287207945103 8077952494038430811917655)
              ·
                refine ⟨12116928741057646217876483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8077952494038430811917655 12116928741057646217876483)
                ·
                  refine ⟨18175393111586469326814725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12116928741057646217876483 18175393111586469326814725)
                  ·
                    refine ⟨3407886208422462998777761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18175393111586469326814725 3407886208422462998777761)
                    ·
                      refine ⟨2555914656316847249083321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3407886208422462998777761 2555914656316847249083321)
                      ·
                        rfl

theorem cell23_4977626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 1, 4, 2].length) (baseStart_4977626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4977626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4977626 prefixEnd_4977626 := by exact prefixLift 4977626
  have htrace : WordTrace (prefixWord ++ tailWord_4977626) baseStart_4977626 baseEnd_4977626 := by
    simpa [prefixWord, tailWord_4977626, baseEnd_4977626] using wordTrace_append hprefix tailTrace_4977626
  have hstable : (prefixWord ++ tailWord_4977626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4977626).length < 2 ^ (prefixWord ++ tailWord_4977626).sum := by decide
  have hdescent : baseEnd_4977626 < baseStart_4977626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4977626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4977649 : List Nat := [1, 2, 2, 2, 4, 1, 3, 3, 5]
def baseStart_4977649 : Nat := 118140960795 + 4977649 * 2 ^ 59
def prefixEnd_4977649 : Nat := 4983230072969 + 3 ^ 40 * 4977649 * 2
def baseEnd_4977649 : Nat := 283991829596877851010635

theorem tailTrace_4977649 : CollatzResearch.WordTrace tailWord_4977649 prefixEnd_4977649 283991829596877851010635 := by
  unfold tailWord_4977649
  simp only [CollatzResearch.WordTrace]
  refine ⟨181549773943835262613216001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121033182629223508408810667 181549773943835262613216001)
  ·
    refine ⟨136162330457876446959912001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181549773943835262613216001 136162330457876446959912001)
    ·
      refine ⟨102121747843407335219934001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136162330457876446959912001 102121747843407335219934001)
      ·
        refine ⟨76591310882555501414950501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102121747843407335219934001 76591310882555501414950501)
        ·
          refine ⟨14360870790479156515303219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76591310882555501414950501 14360870790479156515303219)
          ·
            refine ⟨21541306185718734772954829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14360870790479156515303219 21541306185718734772954829)
            ·
              refine ⟨8077989819644525539858061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21541306185718734772954829 8077989819644525539858061)
              ·
                refine ⟨3029246182366697077446773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8077989819644525539858061 3029246182366697077446773)
                ·
                  refine ⟨283991829596877851010635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3029246182366697077446773 283991829596877851010635)
                  ·
                    rfl

theorem cell23_4977649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 3, 5].length) (baseStart_4977649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4977649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4977649 prefixEnd_4977649 := by exact prefixLift 4977649
  have htrace : WordTrace (prefixWord ++ tailWord_4977649) baseStart_4977649 baseEnd_4977649 := by
    simpa [prefixWord, tailWord_4977649, baseEnd_4977649] using wordTrace_append hprefix tailTrace_4977649
  have hstable : (prefixWord ++ tailWord_4977649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4977649).length < 2 ^ (prefixWord ++ tailWord_4977649).sum := by decide
  have hdescent : baseEnd_4977649 < baseStart_4977649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4977649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4977672 : List Nat := [2, 1, 3, 2, 1, 4, 1, 1, 1, 2, 5]
def baseStart_4977672 : Nat := 118140960795 + 4977672 * 2 ^ 59
def prefixEnd_4977672 : Nat := 4983230072969 + 3 ^ 40 * 4977672 * 2
def baseEnd_4977672 : Nat := 2555938276426954069108109

theorem tailTrace_4977672 : CollatzResearch.WordTrace tailWord_4977672 prefixEnd_4977672 2555938276426954069108109 := by
  unfold tailWord_4977672
  simp only [CollatzResearch.WordTrace]
  refine ⟨90775306411375968770651635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121033741881834625027535513 90775306411375968770651635)
  ·
    refine ⟨136162959617063953155977453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90775306411375968770651635 136162959617063953155977453)
    ·
      refine ⟨51061109856398982433491545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136162959617063953155977453 51061109856398982433491545)
      ·
        refine ⟨38295832392299236825118659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51061109856398982433491545 38295832392299236825118659)
        ·
          refine ⟨57443748588448855237677989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38295832392299236825118659 57443748588448855237677989)
          ·
            refine ⟨10770702860334160357064623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57443748588448855237677989 10770702860334160357064623)
            ·
              refine ⟨16156054290501240535596935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10770702860334160357064623 16156054290501240535596935)
              ·
                refine ⟨24234081435751860803395403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16156054290501240535596935 24234081435751860803395403)
                ·
                  refine ⟨36351122153627791205093105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24234081435751860803395403 36351122153627791205093105)
                  ·
                    refine ⟨27263341615220843403819829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36351122153627791205093105 27263341615220843403819829)
                    ·
                      refine ⟨2555938276426954069108109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27263341615220843403819829 2555938276426954069108109)
                      ·
                        rfl

theorem cell23_4977672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_4977672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4977672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4977672 prefixEnd_4977672 := by exact prefixLift 4977672
  have htrace : WordTrace (prefixWord ++ tailWord_4977672) baseStart_4977672 baseEnd_4977672 := by
    simpa [prefixWord, tailWord_4977672, baseEnd_4977672] using wordTrace_append hprefix tailTrace_4977672
  have hstable : (prefixWord ++ tailWord_4977672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4977672).length < 2 ^ (prefixWord ++ tailWord_4977672).sum := by decide
  have hdescent : baseEnd_4977672 < baseStart_4977672 := by decide
  rcases family_descends (prefixWord ++ tailWord_4977672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4977696 : List Nat := [2, 1, 1, 7, 1, 1, 2, 1, 2, 5]
def baseStart_4977696 : Nat := 118140960795 + 4977696 * 2 ^ 59
def prefixEnd_4977696 : Nat := 4983230072969 + 3 ^ 40 * 4977696 * 2
def baseEnd_4977696 : Nat := 851983533320887325069333

theorem tailTrace_4977696 : CollatzResearch.WordTrace tailWord_4977696 prefixEnd_4977696 851983533320887325069333 := by
  unfold tailWord_4977696
  simp only [CollatzResearch.WordTrace]
  refine ⟨90775744087332494820088471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121034325449776659760117961 90775744087332494820088471)
  ·
    refine ⟨136163616130998742230132707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90775744087332494820088471 136163616130998742230132707)
    ·
      refine ⟨204245424196498113345199061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136163616130998742230132707 204245424196498113345199061)
      ·
        refine ⟨4787002129605424531528103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 204245424196498113345199061 4787002129605424531528103)
        ·
          refine ⟨7180503194408136797292155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4787002129605424531528103 7180503194408136797292155)
          ·
            refine ⟨10770754791612205195938233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7180503194408136797292155 10770754791612205195938233)
            ·
              refine ⟨8078066093709153896953675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10770754791612205195938233 8078066093709153896953675)
              ·
                refine ⟨12117099140563730845430513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8078066093709153896953675 12117099140563730845430513)
                ·
                  refine ⟨9087824355422798134072885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12117099140563730845430513 9087824355422798134072885)
                  ·
                    refine ⟨851983533320887325069333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9087824355422798134072885 851983533320887325069333)
                    ·
                      rfl

theorem cell23_4977696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 1, 2, 5].length) (baseStart_4977696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4977696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4977696 prefixEnd_4977696 := by exact prefixLift 4977696
  have htrace : WordTrace (prefixWord ++ tailWord_4977696) baseStart_4977696 baseEnd_4977696 := by
    simpa [prefixWord, tailWord_4977696, baseEnd_4977696] using wordTrace_append hprefix tailTrace_4977696
  have hstable : (prefixWord ++ tailWord_4977696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4977696).length < 2 ^ (prefixWord ++ tailWord_4977696).sum := by decide
  have hdescent : baseEnd_4977696 < baseStart_4977696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4977696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4977699 : List Nat := [1, 1, 1, 4, 3, 3, 2, 1, 2, 1, 4]
def baseStart_4977699 : Nat := 118140960795 + 4977699 * 2 ^ 59
def prefixEnd_4977699 : Nat := 4983230072969 + 3 ^ 40 * 4977699 * 2
def baseEnd_4977699 : Nat := 2555952140404625463470485

theorem tailTrace_4977699 : CollatzResearch.WordTrace tailWord_4977699 prefixEnd_4977699 2555952140404625463470485 := by
  unfold tailWord_4977699
  simp only [CollatzResearch.WordTrace]
  refine ⟨181551597593654121152536151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121034398395769414101690767 181551597593654121152536151)
  ·
    refine ⟨272327396390481181728804227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181551597593654121152536151 272327396390481181728804227)
    ·
      refine ⟨408491094585721772593206341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272327396390481181728804227 408491094585721772593206341)
      ·
        refine ⟨76592080234822832361226189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 408491094585721772593206341 76592080234822832361226189)
        ·
          refine ⟨28722030088058562135459821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76592080234822832361226189 28722030088058562135459821)
          ·
            refine ⟨10770761283021960800797433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28722030088058562135459821 10770761283021960800797433)
            ·
              refine ⟨8078070962266470600598075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10770761283021960800797433 8078070962266470600598075)
              ·
                refine ⟨12117106443399705900897113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8078070962266470600598075 12117106443399705900897113)
                ·
                  refine ⟨9087829832549779425672835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12117106443399705900897113 9087829832549779425672835)
                  ·
                    refine ⟨13631744748824669138509253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9087829832549779425672835 13631744748824669138509253)
                    ·
                      refine ⟨2555952140404625463470485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13631744748824669138509253 2555952140404625463470485)
                      ·
                        rfl

theorem cell23_4977699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 1, 2, 1, 4].length) (baseStart_4977699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4977699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4977699 prefixEnd_4977699 := by exact prefixLift 4977699
  have htrace : WordTrace (prefixWord ++ tailWord_4977699) baseStart_4977699 baseEnd_4977699 := by
    simpa [prefixWord, tailWord_4977699, baseEnd_4977699] using wordTrace_append hprefix tailTrace_4977699
  have hstable : (prefixWord ++ tailWord_4977699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4977699).length < 2 ^ (prefixWord ++ tailWord_4977699).sum := by decide
  have hdescent : baseEnd_4977699 < baseStart_4977699 := by decide
  rcases family_descends (prefixWord ++ tailWord_4977699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4977716 : List Nat := [2, 5, 1, 2, 1, 1, 2, 2, 2, 1, 4]
def baseStart_4977716 : Nat := 118140960795 + 4977716 * 2 ^ 59
def prefixEnd_4977716 : Nat := 4983230072969 + 3 ^ 40 * 4977716 * 2
def baseEnd_4977716 : Nat := 2555960869575751896957907

theorem tailTrace_4977716 : CollatzResearch.WordTrace tailWord_4977716 prefixEnd_4977716 2555960869575751896957907 := by
  unfold tailWord_4977716
  simp only [CollatzResearch.WordTrace]
  refine ⟨90776108817296266527952501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121034811756395022037270001 90776108817296266527952501)
  ·
    refine ⟨8510260201621524986995547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90776108817296266527952501 8510260201621524986995547)
    ·
      refine ⟨12765390302432287480493321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8510260201621524986995547 12765390302432287480493321)
      ·
        refine ⟨9574042726824215610369991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12765390302432287480493321 9574042726824215610369991)
        ·
          refine ⟨14361064090236323415554987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9574042726824215610369991 14361064090236323415554987)
          ·
            refine ⟨21541596135354485123332481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14361064090236323415554987 21541596135354485123332481)
            ·
              refine ⟨16156197101515863842499361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21541596135354485123332481 16156197101515863842499361)
              ·
                refine ⟨12117147826136897881874521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16156197101515863842499361 12117147826136897881874521)
                ·
                  refine ⟨9087860869602673411405891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12117147826136897881874521 9087860869602673411405891)
                  ·
                    refine ⟨13631791304404010117108837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9087860869602673411405891 13631791304404010117108837)
                    ·
                      refine ⟨2555960869575751896957907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13631791304404010117108837 2555960869575751896957907)
                      ·
                        rfl

theorem cell23_4977716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_4977716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4977716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4977716 prefixEnd_4977716 := by exact prefixLift 4977716
  have htrace : WordTrace (prefixWord ++ tailWord_4977716) baseStart_4977716 baseEnd_4977716 := by
    simpa [prefixWord, tailWord_4977716, baseEnd_4977716] using wordTrace_append hprefix tailTrace_4977716
  have hstable : (prefixWord ++ tailWord_4977716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4977716).length < 2 ^ (prefixWord ++ tailWord_4977716).sum := by decide
  have hdescent : baseEnd_4977716 < baseStart_4977716 := by decide
  rcases family_descends (prefixWord ++ tailWord_4977716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4977722 : List Nat := [3, 1, 1, 1, 3, 1, 3, 4, 6]
def baseStart_4977722 : Nat := 118140960795 + 4977722 * 2 ^ 59
def prefixEnd_4977722 : Nat := 4983230072969 + 3 ^ 40 * 4977722 * 2
def baseEnd_4977722 : Nat := 283995994495519874831431

theorem tailTrace_4977722 : CollatzResearch.WordTrace tailWord_4977722 prefixEnd_4977722 283995994495519874831431 := by
  unfold tailWord_4977722
  simp only [CollatzResearch.WordTrace]
  refine ⟨45388109118142699020155855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121034957648380530720415613 45388109118142699020155855)
  ·
    refine ⟨68082163677214048530233783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45388109118142699020155855 68082163677214048530233783)
    ·
      refine ⟨102123245515821072795350675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68082163677214048530233783 102123245515821072795350675)
      ·
        refine ⟨153184868273731609193026013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102123245515821072795350675 153184868273731609193026013)
        ·
          refine ⟨57444325602649353447384755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153184868273731609193026013 57444325602649353447384755)
          ·
            refine ⟨86166488403974030171077133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57444325602649353447384755 86166488403974030171077133)
            ·
              refine ⟨32312433151490261314153925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86166488403974030171077133 32312433151490261314153925)
              ·
                refine ⟨6058581215904423996403861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32312433151490261314153925 6058581215904423996403861)
                ·
                  refine ⟨283995994495519874831431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6058581215904423996403861 283995994495519874831431)
                  ·
                    rfl

theorem cell23_4977722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 4, 6].length) (baseStart_4977722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4977722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4977722 prefixEnd_4977722 := by exact prefixLift 4977722
  have htrace : WordTrace (prefixWord ++ tailWord_4977722) baseStart_4977722 baseEnd_4977722 := by
    simpa [prefixWord, tailWord_4977722, baseEnd_4977722] using wordTrace_append hprefix tailTrace_4977722
  have hstable : (prefixWord ++ tailWord_4977722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4977722).length < 2 ^ (prefixWord ++ tailWord_4977722).sum := by decide
  have hdescent : baseEnd_4977722 < baseStart_4977722 := by decide
  rcases family_descends (prefixWord ++ tailWord_4977722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4977750 : List Nat := [5, 2, 2, 1, 2, 2, 1, 1, 2, 1, 4]
def baseStart_4977750 : Nat := 118140960795 + 4977750 * 2 ^ 59
def prefixEnd_4977750 : Nat := 4983230072969 + 3 ^ 40 * 4977750 * 2
def baseEnd_4977750 : Nat := 2555978327918004763932751

theorem tailTrace_4977750 : CollatzResearch.WordTrace tailWord_4977750 prefixEnd_4977750 2555978327918004763932751 := by
  unfold tailWord_4977750
  simp only [CollatzResearch.WordTrace]
  refine ⟨11347091107279334803915169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 121035638477646237908428469 11347091107279334803915169)
  ·
    refine ⟨8510318330459501102936377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11347091107279334803915169 8510318330459501102936377)
    ·
      refine ⟨6382738747844625827202283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8510318330459501102936377 6382738747844625827202283)
      ·
        refine ⟨9574108121766938740803425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6382738747844625827202283 9574108121766938740803425)
        ·
          refine ⟨7180581091325204055602569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9574108121766938740803425 7180581091325204055602569)
          ·
            refine ⟨5385435818493903041701927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7180581091325204055602569 5385435818493903041701927)
            ·
              refine ⟨8078153727740854562552891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5385435818493903041701927 8078153727740854562552891)
              ·
                refine ⟨12117230591611281843829337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8078153727740854562552891 12117230591611281843829337)
                ·
                  refine ⟨9087922943708461382872003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12117230591611281843829337 9087922943708461382872003)
                  ·
                    refine ⟨13631884415562692074308005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9087922943708461382872003 13631884415562692074308005)
                    ·
                      refine ⟨2555978327918004763932751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13631884415562692074308005 2555978327918004763932751)
                      ·
                        rfl

theorem cell23_4977750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_4977750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4977750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4977750 prefixEnd_4977750 := by exact prefixLift 4977750
  have htrace : WordTrace (prefixWord ++ tailWord_4977750) baseStart_4977750 baseEnd_4977750 := by
    simpa [prefixWord, tailWord_4977750, baseEnd_4977750] using wordTrace_append hprefix tailTrace_4977750
  have hstable : (prefixWord ++ tailWord_4977750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4977750).length < 2 ^ (prefixWord ++ tailWord_4977750).sum := by decide
  have hdescent : baseEnd_4977750 < baseStart_4977750 := by decide
  rcases family_descends (prefixWord ++ tailWord_4977750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4977752 : List Nat := [2, 1, 2, 2, 1, 3, 1, 3, 3, 5]
def baseStart_4977752 : Nat := 118140960795 + 4977752 * 2 ^ 59
def prefixEnd_4977752 : Nat := 4983230072969 + 3 ^ 40 * 4977752 * 2
def baseEnd_4977752 : Nat := 851993118293104585369247

theorem tailTrace_4977752 : CollatzResearch.WordTrace tailWord_4977752 prefixEnd_4977752 851993118293104585369247 := by
  unfold tailWord_4977752
  simp only [CollatzResearch.WordTrace]
  refine ⟨90776765331231055602107755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121035687108308074136143673 90776765331231055602107755)
  ·
    refine ⟨136165147996846583403161633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90776765331231055602107755 136165147996846583403161633)
    ·
      refine ⟨102123860997634937552371225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136165147996846583403161633 102123860997634937552371225)
      ·
        refine ⟨76592895748226203164278419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102123860997634937552371225 76592895748226203164278419)
        ·
          refine ⟨114889343622339304746417629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76592895748226203164278419 114889343622339304746417629)
          ·
            refine ⟨43083503858377239279906611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114889343622339304746417629 43083503858377239279906611)
            ·
              refine ⟨64625255787565858919859917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43083503858377239279906611 64625255787565858919859917)
              ·
                refine ⟨24234470920337197094947469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64625255787565858919859917 24234470920337197094947469)
                ·
                  refine ⟨9087926595126448910605301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24234470920337197094947469 9087926595126448910605301)
                  ·
                    refine ⟨851993118293104585369247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9087926595126448910605301 851993118293104585369247)
                    ·
                      rfl

theorem cell23_4977752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 3, 5].length) (baseStart_4977752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4977752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4977752 prefixEnd_4977752 := by exact prefixLift 4977752
  have htrace : WordTrace (prefixWord ++ tailWord_4977752) baseStart_4977752 baseEnd_4977752 := by
    simpa [prefixWord, tailWord_4977752, baseEnd_4977752] using wordTrace_append hprefix tailTrace_4977752
  have hstable : (prefixWord ++ tailWord_4977752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4977752).length < 2 ^ (prefixWord ++ tailWord_4977752).sum := by decide
  have hdescent : baseEnd_4977752 < baseStart_4977752 := by decide
  rcases family_descends (prefixWord ++ tailWord_4977752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4977759 : List Nat := [1, 1, 2, 3, 1, 1, 5, 1, 1, 5, 2]
def baseStart_4977759 : Nat := 118140960795 + 4977759 * 2 ^ 59
def prefixEnd_4977759 : Nat := 4983230072969 + 3 ^ 40 * 4977759 * 2
def baseEnd_4977759 : Nat := 2555982949243895228720209

theorem tailTrace_4977759 : CollatzResearch.WordTrace tailWord_4977759 prefixEnd_4977759 2555982949243895228720209 := by
  unfold tailWord_4977759
  simp only [CollatzResearch.WordTrace]
  refine ⟨181553785973436751399720331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121035857315624500933146887 181553785973436751399720331)
  ·
    refine ⟨272330678960155127099580497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181553785973436751399720331 272330678960155127099580497)
    ·
      refine ⟨204248009220116345324685373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 272330678960155127099580497 204248009220116345324685373)
      ·
        refine ⟨76593003457543629496757015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 204248009220116345324685373 76593003457543629496757015)
        ·
          refine ⟨114889505186315444245135523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76593003457543629496757015 114889505186315444245135523)
          ·
            refine ⟨172334257779473166367703285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114889505186315444245135523 172334257779473166367703285)
            ·
              refine ⟨16156336666825609346972183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 172334257779473166367703285 16156336666825609346972183)
              ·
                refine ⟨24234505000238414020458275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16156336666825609346972183 24234505000238414020458275)
                ·
                  refine ⟨36351757500357621030687413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24234505000238414020458275 36351757500357621030687413)
                  ·
                    refine ⟨3407977265658526971626945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36351757500357621030687413 3407977265658526971626945)
                    ·
                      refine ⟨2555982949243895228720209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3407977265658526971626945 2555982949243895228720209)
                      ·
                        rfl

theorem cell23_4977759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 5, 2].length) (baseStart_4977759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4977759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4977759 prefixEnd_4977759 := by exact prefixLift 4977759
  have htrace : WordTrace (prefixWord ++ tailWord_4977759) baseStart_4977759 baseEnd_4977759 := by
    simpa [prefixWord, tailWord_4977759, baseEnd_4977759] using wordTrace_append hprefix tailTrace_4977759
  have hstable : (prefixWord ++ tailWord_4977759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4977759).length < 2 ^ (prefixWord ++ tailWord_4977759).sum := by decide
  have hdescent : baseEnd_4977759 < baseStart_4977759 := by decide
  rcases family_descends (prefixWord ++ tailWord_4977759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4977769 : List Nat := [1, 2, 1, 1, 1, 7, 1, 3, 1, 5]
def baseStart_4977769 : Nat := 118140960795 + 4977769 * 2 ^ 59
def prefixEnd_4977769 : Nat := 4983230072969 + 3 ^ 40 * 4977769 * 2
def baseEnd_4977769 : Nat := 851996028016813396531721

theorem tailTrace_4977769 : CollatzResearch.WordTrace tailWord_4977769 prefixEnd_4977769 851996028016813396531721 := by
  unfold tailWord_4977769
  simp only [CollatzResearch.WordTrace]
  refine ⟨181554150703400523107584361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121036100468933682071722907 181554150703400523107584361)
  ·
    refine ⟨136165613027550392330688271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181554150703400523107584361 136165613027550392330688271)
    ·
      refine ⟨204248419541325588496032407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136165613027550392330688271 204248419541325588496032407)
      ·
        refine ⟨306372629311988382744048611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204248419541325588496032407 306372629311988382744048611)
        ·
          refine ⟨459558943967982574116072917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 306372629311988382744048611 459558943967982574116072917)
          ·
            refine ⟨10770912749249591580845459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 459558943967982574116072917 10770912749249591580845459)
            ·
              refine ⟨16156369123874387371268189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10770912749249591580845459 16156369123874387371268189)
              ·
                refine ⟨6058638421452895264225571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16156369123874387371268189 6058638421452895264225571)
                ·
                  refine ⟨9087957632179342896338357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6058638421452895264225571 9087957632179342896338357)
                  ·
                    refine ⟨851996028016813396531721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9087957632179342896338357 851996028016813396531721)
                    ·
                      rfl

theorem cell23_4977769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 3, 1, 5].length) (baseStart_4977769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4977769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4977769 prefixEnd_4977769 := by exact prefixLift 4977769
  have htrace : WordTrace (prefixWord ++ tailWord_4977769) baseStart_4977769 baseEnd_4977769 := by
    simpa [prefixWord, tailWord_4977769, baseEnd_4977769] using wordTrace_append hprefix tailTrace_4977769
  have hstable : (prefixWord ++ tailWord_4977769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4977769).length < 2 ^ (prefixWord ++ tailWord_4977769).sum := by decide
  have hdescent : baseEnd_4977769 < baseStart_4977769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4977769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4977792 : List Nat := [2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 5]
def baseStart_4977792 : Nat := 118140960795 + 4977792 * 2 ^ 59
def prefixEnd_4977792 : Nat := 4983230072969 + 3 ^ 40 * 4977792 * 2
def baseEnd_4977792 : Nat := 2555999894105493599607557

theorem tailTrace_4977792 : CollatzResearch.WordTrace tailWord_4977792 prefixEnd_4977792 2555999894105493599607557 := by
  unfold tailWord_4977792
  simp only [CollatzResearch.WordTrace]
  refine ⟨90777494791158599017835815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121036659721544798690447753 90777494791158599017835815)
  ·
    refine ⟨136166242186737898526753723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90777494791158599017835815 136166242186737898526753723)
    ·
      refine ⟨204249363280106847790130585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136166242186737898526753723 204249363280106847790130585)
      ·
        refine ⟨153187022460080135842597939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204249363280106847790130585 153187022460080135842597939)
        ·
          refine ⟨229780533690120203763896909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153187022460080135842597939 229780533690120203763896909)
          ·
            refine ⟨86167700133795076411461341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 229780533690120203763896909 86167700133795076411461341)
            ·
              refine ⟨32312887550173153654298003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86167700133795076411461341 32312887550173153654298003)
              ·
                refine ⟨48469331325259730481447005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32312887550173153654298003 48469331325259730481447005)
                ·
                  refine ⟨18175999246972398930542627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48469331325259730481447005 18175999246972398930542627)
                  ·
                    refine ⟨27263998870458598395813941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18175999246972398930542627 27263998870458598395813941)
                    ·
                      refine ⟨2555999894105493599607557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27263998870458598395813941 2555999894105493599607557)
                      ·
                        rfl

theorem cell23_4977792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 5].length) (baseStart_4977792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4977792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4977792 prefixEnd_4977792 := by exact prefixLift 4977792
  have htrace : WordTrace (prefixWord ++ tailWord_4977792) baseStart_4977792 baseEnd_4977792 := by
    simpa [prefixWord, tailWord_4977792, baseEnd_4977792] using wordTrace_append hprefix tailTrace_4977792
  have hstable : (prefixWord ++ tailWord_4977792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4977792).length < 2 ^ (prefixWord ++ tailWord_4977792).sum := by decide
  have hdescent : baseEnd_4977792 < baseStart_4977792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4977792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4977806 : List Nat := [4, 1, 1, 3, 2, 1, 1, 4, 1, 1, 4]
def baseStart_4977806 : Nat := 118140960795 + 4977806 * 2 ^ 59
def prefixEnd_4977806 : Nat := 4983230072969 + 3 ^ 40 * 4977806 * 2
def baseEnd_4977806 : Nat := 2556007082834656544832493

theorem tailTrace_4977806 : CollatzResearch.WordTrace tailWord_4977806 prefixEnd_4977806 2556007082834656544832493 := by
  unfold tailWord_4977806
  simp only [CollatzResearch.WordTrace]
  refine ⟨22694437525533309803335159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121037000136177652284454181 22694437525533309803335159)
  ·
    refine ⟨34041656288299964705002739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22694437525533309803335159 34041656288299964705002739)
    ·
      refine ⟨51062484432449947057504109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34041656288299964705002739 51062484432449947057504109)
      ·
        refine ⟨19148431662168730146564041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51062484432449947057504109 19148431662168730146564041)
        ·
          refine ⟨14361323746626547609923031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19148431662168730146564041 14361323746626547609923031)
          ·
            refine ⟨21541985619939821414884547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14361323746626547609923031 21541985619939821414884547)
            ·
              refine ⟨32312978429909732122326821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21541985619939821414884547 32312978429909732122326821)
              ·
                refine ⟨6058683455608074772936279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32312978429909732122326821 6058683455608074772936279)
                ·
                  refine ⟨9088025183412112159404419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6058683455608074772936279 9088025183412112159404419)
                  ·
                    refine ⟨13632037775118168239106629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9088025183412112159404419 13632037775118168239106629)
                    ·
                      refine ⟨2556007082834656544832493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13632037775118168239106629 2556007082834656544832493)
                      ·
                        rfl

theorem cell23_4977806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_4977806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4977806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4977806 prefixEnd_4977806 := by exact prefixLift 4977806
  have htrace : WordTrace (prefixWord ++ tailWord_4977806) baseStart_4977806 baseEnd_4977806 := by
    simpa [prefixWord, tailWord_4977806, baseEnd_4977806] using wordTrace_append hprefix tailTrace_4977806
  have hstable : (prefixWord ++ tailWord_4977806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4977806).length < 2 ^ (prefixWord ++ tailWord_4977806).sum := by decide
  have hdescent : baseEnd_4977806 < baseStart_4977806 := by decide
  rcases family_descends (prefixWord ++ tailWord_4977806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4977860 : List Nat := [2, 3, 3, 1, 3, 2, 1, 2, 1, 2, 3]
def baseStart_4977860 : Nat := 118140960795 + 4977860 * 2 ^ 59
def prefixEnd_4977860 : Nat := 4983230072969 + 3 ^ 40 * 4977860 * 2
def baseEnd_4977860 : Nat := 2556034810789999333557245

theorem tailTrace_4977860 : CollatzResearch.WordTrace tailWord_4977860 prefixEnd_4977860 2556034810789999333557245 := by
  unfold tailWord_4977860
  simp only [CollatzResearch.WordTrace]
  refine ⟨90778734873035422824573517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121038313164047230432764689 90778734873035422824573517)
  ·
    refine ⟨34042025577388283559215069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90778734873035422824573517 34042025577388283559215069)
    ·
      refine ⟨12765759591520606334705651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34042025577388283559215069 12765759591520606334705651)
      ·
        refine ⟨19148639387280909502058477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12765759591520606334705651 19148639387280909502058477)
        ·
          refine ⟨7180739770230341063271929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19148639387280909502058477 7180739770230341063271929)
          ·
            refine ⟨5385554827672755797453947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7180739770230341063271929 5385554827672755797453947)
            ·
              refine ⟨8078332241509133696180921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5385554827672755797453947 8078332241509133696180921)
              ·
                refine ⟨6058749181131850272135691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8078332241509133696180921 6058749181131850272135691)
                ·
                  refine ⟨9088123771697775408203537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6058749181131850272135691 9088123771697775408203537)
                  ·
                    refine ⟨6816092828773331556152653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9088123771697775408203537 6816092828773331556152653)
                    ·
                      refine ⟨2556034810789999333557245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6816092828773331556152653 2556034810789999333557245)
                      ·
                        rfl

theorem cell23_4977860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_4977860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4977860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4977860 prefixEnd_4977860 := by exact prefixLift 4977860
  have htrace : WordTrace (prefixWord ++ tailWord_4977860) baseStart_4977860 baseEnd_4977860 := by
    simpa [prefixWord, tailWord_4977860, baseEnd_4977860] using wordTrace_append hprefix tailTrace_4977860
  have hstable : (prefixWord ++ tailWord_4977860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4977860).length < 2 ^ (prefixWord ++ tailWord_4977860).sum := by decide
  have hdescent : baseEnd_4977860 < baseStart_4977860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4977860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4977896 : List Nat := [2, 1, 4, 1, 2, 1, 1, 2, 3, 4, 2]
def baseStart_4977896 : Nat := 118140960795 + 4977896 * 2 ^ 59
def prefixEnd_4977896 : Nat := 4983230072969 + 3 ^ 40 * 4977896 * 2
def baseEnd_4977896 : Nat := 2556053296093561192707079

theorem tailTrace_4977896 : CollatzResearch.WordTrace tailWord_4977896 prefixEnd_4977896 2556053296093561192707079 := by
  unfold tailWord_4977896
  simp only [CollatzResearch.WordTrace]
  refine ⟨90779391386970211898728771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121039188515960282531638361 90779391386970211898728771)
  ·
    refine ⟨136169087080455317848093157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90779391386970211898728771 136169087080455317848093157)
    ·
      refine ⟨25531703827585372096517467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 136169087080455317848093157 25531703827585372096517467)
      ·
        refine ⟨38297555741378058144776201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25531703827585372096517467 38297555741378058144776201)
        ·
          refine ⟨28723166806033543608582151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38297555741378058144776201 28723166806033543608582151)
          ·
            refine ⟨43084750209050315412873227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28723166806033543608582151 43084750209050315412873227)
            ·
              refine ⟨64627125313575473119309841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43084750209050315412873227 64627125313575473119309841)
              ·
                refine ⟨48470343985181604839482381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64627125313575473119309841 48470343985181604839482381)
                ·
                  refine ⟨18176378994443101814805893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48470343985181604839482381 18176378994443101814805893)
                  ·
                    refine ⟨3408071061458081590276105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18176378994443101814805893 3408071061458081590276105)
                    ·
                      refine ⟨2556053296093561192707079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3408071061458081590276105 2556053296093561192707079)
                      ·
                        rfl

theorem cell23_4977896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 3, 4, 2].length) (baseStart_4977896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4977896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4977896 prefixEnd_4977896 := by exact prefixLift 4977896
  have htrace : WordTrace (prefixWord ++ tailWord_4977896) baseStart_4977896 baseEnd_4977896 := by
    simpa [prefixWord, tailWord_4977896, baseEnd_4977896] using wordTrace_append hprefix tailTrace_4977896
  have hstable : (prefixWord ++ tailWord_4977896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4977896).length < 2 ^ (prefixWord ++ tailWord_4977896).sum := by decide
  have hdescent : baseEnd_4977896 < baseStart_4977896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4977896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4977899 : List Nat := [1, 1, 1, 1, 2, 6, 1, 1, 2, 4, 3]
def baseStart_4977899 : Nat := 118140960795 + 4977899 * 2 ^ 59
def prefixEnd_4977899 : Nat := 4983230072969 + 3 ^ 40 * 4977899 * 2
def baseEnd_4977899 : Nat := 2556054836535524680969565

theorem tailTrace_4977899 : CollatzResearch.WordTrace tailWord_4977899 prefixEnd_4977899 2556054836535524680969565 := by
  unfold tailWord_4977899
  simp only [CollatzResearch.WordTrace]
  refine ⟨181558892192929555309816751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121039261461953036873211167 181558892192929555309816751)
  ·
    refine ⟨272338338289394332964725127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181558892192929555309816751 272338338289394332964725127)
    ·
      refine ⟨408507507434091499447087691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272338338289394332964725127 408507507434091499447087691)
      ·
        refine ⟨612761261151137249170631537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 408507507434091499447087691 612761261151137249170631537)
        ·
          refine ⟨459570945863352936877973653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 612761261151137249170631537 459570945863352936877973653)
          ·
            refine ⟨21542388087344668916155015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 459570945863352936877973653 21542388087344668916155015)
            ·
              refine ⟨32313582131017003374232523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21542388087344668916155015 32313582131017003374232523)
              ·
                refine ⟨48470373196525505061348785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32313582131017003374232523 48470373196525505061348785)
                ·
                  refine ⟨36352779897394128796011589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48470373196525505061348785 36352779897394128796011589)
                  ·
                    refine ⟨6816146230761399149252173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36352779897394128796011589 6816146230761399149252173)
                    ·
                      refine ⟨2556054836535524680969565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6816146230761399149252173 2556054836535524680969565)
                      ·
                        rfl

theorem cell23_4977899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 4, 3].length) (baseStart_4977899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4977899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4977899 prefixEnd_4977899 := by exact prefixLift 4977899
  have htrace : WordTrace (prefixWord ++ tailWord_4977899) baseStart_4977899 baseEnd_4977899 := by
    simpa [prefixWord, tailWord_4977899, baseEnd_4977899] using wordTrace_append hprefix tailTrace_4977899
  have hstable : (prefixWord ++ tailWord_4977899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4977899).length < 2 ^ (prefixWord ++ tailWord_4977899).sum := by decide
  have hdescent : baseEnd_4977899 < baseStart_4977899 := by decide
  rcases family_descends (prefixWord ++ tailWord_4977899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4977906 : List Nat := [3, 2, 1, 3, 3, 1, 1, 1, 2, 6]
def baseStart_4977906 : Nat := 118140960795 + 4977906 * 2 ^ 59
def prefixEnd_4977906 : Nat := 4983230072969 + 3 ^ 40 * 4977906 * 2
def baseEnd_4977906 : Nat := 852019476966702051194011

theorem tailTrace_4977906 : CollatzResearch.WordTrace tailWord_4977906 prefixEnd_4977906 852019476966702051194011 := by
  unfold tailWord_4977906
  simp only [CollatzResearch.WordTrace]
  refine ⟨45389786875976048876330393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121039431669269463670214381 45389786875976048876330393)
  ·
    refine ⟨34042340156982036657247795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45389786875976048876330393 34042340156982036657247795)
    ·
      refine ⟨51063510235473054985871693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34042340156982036657247795 51063510235473054985871693)
      ·
        refine ⟨19148816338302395619701885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51063510235473054985871693 19148816338302395619701885)
        ·
          refine ⟨7180806126863398357388207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19148816338302395619701885 7180806126863398357388207)
          ·
            refine ⟨10771209190295097536082311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7180806126863398357388207 10771209190295097536082311)
            ·
              refine ⟨16156813785442646304123467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10771209190295097536082311 16156813785442646304123467)
              ·
                refine ⟨24235220678163969456185201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16156813785442646304123467 24235220678163969456185201)
                ·
                  refine ⟨18176415508622977092138901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24235220678163969456185201 18176415508622977092138901)
                  ·
                    refine ⟨852019476966702051194011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18176415508622977092138901 852019476966702051194011)
                    ·
                      rfl

theorem cell23_4977906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 2, 6].length) (baseStart_4977906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4977906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4977906 prefixEnd_4977906 := by exact prefixLift 4977906
  have htrace : WordTrace (prefixWord ++ tailWord_4977906) baseStart_4977906 baseEnd_4977906 := by
    simpa [prefixWord, tailWord_4977906, baseEnd_4977906] using wordTrace_append hprefix tailTrace_4977906
  have hstable : (prefixWord ++ tailWord_4977906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4977906).length < 2 ^ (prefixWord ++ tailWord_4977906).sum := by decide
  have hdescent : baseEnd_4977906 < baseStart_4977906 := by decide
  rcases family_descends (prefixWord ++ tailWord_4977906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4977913 : List Nat := [1, 2, 1, 3, 1, 1, 3, 5, 2, 2, 2]
def baseStart_4977913 : Nat := 118140960795 + 4977913 * 2 ^ 59
def prefixEnd_4977913 : Nat := 4983230072969 + 3 ^ 40 * 4977913 * 2
def baseEnd_4977913 : Nat := 2556062025264687626194501

theorem tailTrace_4977913 : CollatzResearch.WordTrace tailWord_4977913 prefixEnd_4977913 2556062025264687626194501 := by
  unfold tailWord_4977913
  simp only [CollatzResearch.WordTrace]
  refine ⟨181559402814878835700826393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121039601876585890467217595 181559402814878835700826393)
  ·
    refine ⟨136169552111159126775619795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181559402814878835700826393 136169552111159126775619795)
    ·
      refine ⟨204254328166738690163429693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136169552111159126775619795 204254328166738690163429693)
      ·
        refine ⟨76595373062527008811286135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 204254328166738690163429693 76595373062527008811286135)
        ·
          refine ⟨114893059593790513216929203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76595373062527008811286135 114893059593790513216929203)
          ·
            refine ⟨172339589390685769825393805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114893059593790513216929203 172339589390685769825393805)
            ·
              refine ⟨64627346021507163684522677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 172339589390685769825393805 64627346021507163684522677)
              ·
                refine ⟨6058813689516296595424001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64627346021507163684522677 6058813689516296595424001)
                ·
                  refine ⟨4544110267137222446568001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6058813689516296595424001 4544110267137222446568001)
                  ·
                    refine ⟨3408082700352916834926001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4544110267137222446568001 3408082700352916834926001)
                    ·
                      refine ⟨2556062025264687626194501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3408082700352916834926001 2556062025264687626194501)
                      ·
                        rfl

theorem cell23_4977913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 5, 2, 2, 2].length) (baseStart_4977913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4977913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4977913 prefixEnd_4977913 := by exact prefixLift 4977913
  have htrace : WordTrace (prefixWord ++ tailWord_4977913) baseStart_4977913 baseEnd_4977913 := by
    simpa [prefixWord, tailWord_4977913, baseEnd_4977913] using wordTrace_append hprefix tailTrace_4977913
  have hstable : (prefixWord ++ tailWord_4977913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4977913).length < 2 ^ (prefixWord ++ tailWord_4977913).sum := by decide
  have hdescent : baseEnd_4977913 < baseStart_4977913 := by decide
  rcases family_descends (prefixWord ++ tailWord_4977913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4977919 : List Nat := [1, 1, 2, 2, 1, 6, 1, 2, 7]
def baseStart_4977919 : Nat := 118140960795 + 4977919 * 2 ^ 59
def prefixEnd_4977919 : Nat := 4983230072969 + 3 ^ 40 * 4977919 * 2
def baseEnd_4977919 : Nat := 284007234016512733635497

theorem tailTrace_4977919 : CollatzResearch.WordTrace tailWord_4977919 prefixEnd_4977919 284007234016512733635497 := by
  unfold tailWord_4977919
  simp only [CollatzResearch.WordTrace]
  refine ⟨181559621652857098725544811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121039747768571399150363207 181559621652857098725544811)
  ·
    refine ⟨272339432479285648088317217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181559621652857098725544811 272339432479285648088317217)
    ·
      refine ⟨204254574359464236066237913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 272339432479285648088317217 204254574359464236066237913)
      ·
        refine ⟨153190930769598177049678435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204254574359464236066237913 153190930769598177049678435)
        ·
          refine ⟨229786396154397265574517653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153190930769598177049678435 229786396154397265574517653)
          ·
            refine ⟨10771237319737371823805515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 229786396154397265574517653 10771237319737371823805515)
            ·
              refine ⟨16156855979606057735708273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10771237319737371823805515 16156855979606057735708273)
              ·
                refine ⟨12117641984704543301781205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16156855979606057735708273 12117641984704543301781205)
                ·
                  refine ⟨284007234016512733635497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12117641984704543301781205 284007234016512733635497)
                  ·
                    rfl

theorem cell23_4977919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 2, 7].length) (baseStart_4977919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4977919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4977919 prefixEnd_4977919 := by exact prefixLift 4977919
  have htrace : WordTrace (prefixWord ++ tailWord_4977919) baseStart_4977919 baseEnd_4977919 := by
    simpa [prefixWord, tailWord_4977919, baseEnd_4977919] using wordTrace_append hprefix tailTrace_4977919
  have hstable : (prefixWord ++ tailWord_4977919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4977919).length < 2 ^ (prefixWord ++ tailWord_4977919).sum := by decide
  have hdescent : baseEnd_4977919 < baseStart_4977919 := by decide
  rcases family_descends (prefixWord ++ tailWord_4977919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4977929 : List Nat := [1, 2, 1, 1, 3, 3, 1, 2, 1, 5, 3]
def baseStart_4977929 : Nat := 118140960795 + 4977929 * 2 ^ 59
def prefixEnd_4977929 : Nat := 4983230072969 + 3 ^ 40 * 4977929 * 2
def baseEnd_4977929 : Nat := 2556070240955159563594427

theorem tailTrace_4977929 : CollatzResearch.WordTrace tailWord_4977929 prefixEnd_4977929 2556070240955159563594427 := by
  unfold tailWord_4977929
  simp only [CollatzResearch.WordTrace]
  refine ⟨181559986382820870433408841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121039990921880580288939227 181559986382820870433408841)
  ·
    refine ⟨136169989787115652825056631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181559986382820870433408841 136169989787115652825056631)
    ·
      refine ⟨204254984680673479237584947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136169989787115652825056631 204254984680673479237584947)
      ·
        refine ⟨306382477021010218856377421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204254984680673479237584947 306382477021010218856377421)
        ·
          refine ⟨114893428882878832071141533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 306382477021010218856377421 114893428882878832071141533)
          ·
            refine ⟨43085035831079562026678075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114893428882878832071141533 43085035831079562026678075)
            ·
              refine ⟨64627553746619343040017113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43085035831079562026678075 64627553746619343040017113)
              ·
                refine ⟨48470665309964507280012835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64627553746619343040017113 48470665309964507280012835)
                ·
                  refine ⟨72705997964946760920019253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48470665309964507280012835 72705997964946760920019253)
                  ·
                    refine ⟨6816187309213758836251805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 72705997964946760920019253 6816187309213758836251805)
                    ·
                      refine ⟨2556070240955159563594427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6816187309213758836251805 2556070240955159563594427)
                      ·
                        rfl

theorem cell23_4977929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 5, 3].length) (baseStart_4977929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4977929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4977929 prefixEnd_4977929 := by exact prefixLift 4977929
  have htrace : WordTrace (prefixWord ++ tailWord_4977929) baseStart_4977929 baseEnd_4977929 := by
    simpa [prefixWord, tailWord_4977929, baseEnd_4977929] using wordTrace_append hprefix tailTrace_4977929
  have hstable : (prefixWord ++ tailWord_4977929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4977929).length < 2 ^ (prefixWord ++ tailWord_4977929).sum := by decide
  have hdescent : baseEnd_4977929 < baseStart_4977929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4977929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4977946 : List Nat := [3, 1, 1, 3, 3, 1, 1, 2, 2, 3, 3]
def baseStart_4977946 : Nat := 118140960795 + 4977946 * 2 ^ 59
def prefixEnd_4977946 : Nat := 4983230072969 + 3 ^ 40 * 4977946 * 2
def baseEnd_4977946 : Nat := 2556078970126285997081849

theorem tailTrace_4977946 : CollatzResearch.WordTrace tailWord_4977946 prefixEnd_4977946 2556078970126285997081849 := by
  unfold tailWord_4977946
  simp only [CollatzResearch.WordTrace]
  refine ⟨45390151605939820584194423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121040404282506188224518461 45390151605939820584194423)
  ·
    refine ⟨68085227408909730876291635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45390151605939820584194423 68085227408909730876291635)
    ·
      refine ⟨102127841113364596314437453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68085227408909730876291635 102127841113364596314437453)
      ·
        refine ⟨38297940417511723617914045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102127841113364596314437453 38297940417511723617914045)
        ·
          refine ⟨14361727656566896356717767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38297940417511723617914045 14361727656566896356717767)
          ·
            refine ⟨21542591484850344535076651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14361727656566896356717767 21542591484850344535076651)
            ·
              refine ⟨32313887227275516802614977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21542591484850344535076651 32313887227275516802614977)
              ·
                refine ⟨24235415420456637601961233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32313887227275516802614977 24235415420456637601961233)
                ·
                  refine ⟨18176561565342478201470925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24235415420456637601961233 18176561565342478201470925)
                  ·
                    refine ⟨6816210587003429325551597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18176561565342478201470925 6816210587003429325551597)
                    ·
                      refine ⟨2556078970126285997081849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6816210587003429325551597 2556078970126285997081849)
                      ·
                        rfl

theorem cell23_4977946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_4977946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4977946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4977946 prefixEnd_4977946 := by exact prefixLift 4977946
  have htrace : WordTrace (prefixWord ++ tailWord_4977946) baseStart_4977946 baseEnd_4977946 := by
    simpa [prefixWord, tailWord_4977946, baseEnd_4977946] using wordTrace_append hprefix tailTrace_4977946
  have hstable : (prefixWord ++ tailWord_4977946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4977946).length < 2 ^ (prefixWord ++ tailWord_4977946).sum := by decide
  have hdescent : baseEnd_4977946 < baseStart_4977946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4977946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4978009 : List Nat := [1, 2, 1, 2, 2, 2, 4, 1, 8]
def baseStart_4978009 : Nat := 118140960795 + 4978009 * 2 ^ 59
def prefixEnd_4978009 : Nat := 4983230072969 + 3 ^ 40 * 4978009 * 2
def baseEnd_4978009 : Nat := 284012368823057694510451

theorem tailTrace_4978009 : CollatzResearch.WordTrace tailWord_4978009 prefixEnd_4978009 284012368823057694510451 := by
  unfold tailWord_4978009
  simp only [CollatzResearch.WordTrace]
  refine ⟨181562904222531044096321081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121041936148354029397547387 181562904222531044096321081)
  ·
    refine ⟨136172178166898283072240811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181562904222531044096321081 136172178166898283072240811)
    ·
      refine ⟨204258267250347424608361217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136172178166898283072240811 204258267250347424608361217)
      ·
        refine ⟨153193700437760568456270913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204258267250347424608361217 153193700437760568456270913)
        ·
          refine ⟨114895275328320426342203185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153193700437760568456270913 114895275328320426342203185)
          ·
            refine ⟨86171456496240319756652389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114895275328320426342203185 86171456496240319756652389)
            ·
              refine ⟨16157148093045059954372323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86171456496240319756652389 16157148093045059954372323)
              ·
                refine ⟨24235722139567589931558485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16157148093045059954372323 24235722139567589931558485)
                ·
                  refine ⟨284012368823057694510451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24235722139567589931558485 284012368823057694510451)
                  ·
                    rfl

theorem cell23_4978009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 8].length) (baseStart_4978009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4978009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4978009 prefixEnd_4978009 := by exact prefixLift 4978009
  have htrace : WordTrace (prefixWord ++ tailWord_4978009) baseStart_4978009 baseEnd_4978009 := by
    simpa [prefixWord, tailWord_4978009, baseEnd_4978009] using wordTrace_append hprefix tailTrace_4978009
  have hstable : (prefixWord ++ tailWord_4978009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4978009).length < 2 ^ (prefixWord ++ tailWord_4978009).sum := by decide
  have hdescent : baseEnd_4978009 < baseStart_4978009 := by decide
  rcases family_descends (prefixWord ++ tailWord_4978009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4978099 : List Nat := [1, 1, 1, 2, 3, 1, 1, 13]
def baseStart_4978099 : Nat := 118140960795 + 4978099 * 2 ^ 59
def prefixEnd_4978099 : Nat := 4983230072969 + 3 ^ 40 * 4978099 * 2
def baseEnd_4978099 : Nat := 94672501209867551795135

theorem tailTrace_4978099 : CollatzResearch.WordTrace tailWord_4978099 prefixEnd_4978099 94672501209867551795135 := by
  unfold tailWord_4978099
  simp only [CollatzResearch.WordTrace]
  refine ⟨181566186792204989467097351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121044124528136659644731567 181566186792204989467097351)
  ·
    refine ⟨272349280188307484200646027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181566186792204989467097351 272349280188307484200646027)
    ·
      refine ⟨408523920282461226300969041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272349280188307484200646027 408523920282461226300969041)
      ·
        refine ⟨306392940211845919725726781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 408523920282461226300969041 306392940211845919725726781)
        ·
          refine ⟨114897352579442219897147543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 306392940211845919725726781 114897352579442219897147543)
          ·
            refine ⟨172346028869163329845721315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114897352579442219897147543 172346028869163329845721315)
            ·
              refine ⟨258519043303744994768581973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172346028869163329845721315 258519043303744994768581973)
              ·
                refine ⟨94672501209867551795135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 258519043303744994768581973 94672501209867551795135)
                ·
                  rfl

theorem cell23_4978099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 13].length) (baseStart_4978099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4978099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4978099 prefixEnd_4978099 := by exact prefixLift 4978099
  have htrace : WordTrace (prefixWord ++ tailWord_4978099) baseStart_4978099 baseEnd_4978099 := by
    simpa [prefixWord, tailWord_4978099, baseEnd_4978099] using wordTrace_append hprefix tailTrace_4978099
  have hstable : (prefixWord ++ tailWord_4978099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4978099).length < 2 ^ (prefixWord ++ tailWord_4978099).sum := by decide
  have hdescent : baseEnd_4978099 < baseStart_4978099 := by decide
  rcases family_descends (prefixWord ++ tailWord_4978099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4978110 : List Nat := [4, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2]
def baseStart_4978110 : Nat := 118140960795 + 4978110 * 2 ^ 59
def prefixEnd_4978110 : Nat := 4983230072969 + 3 ^ 40 * 4978110 * 2
def baseEnd_4978110 : Nat := 2556163180953623355431095

theorem tailTrace_4978110 : CollatzResearch.WordTrace tailWord_4978110 prefixEnd_4978110 2556163180953623355431095 := by
  unfold tailWord_4978110
  simp only [CollatzResearch.WordTrace]
  refine ⟨22695823499395642293218473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121044391996776758897165189 22695823499395642293218473)
  ·
    refine ⟨17021867624546731719913855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22695823499395642293218473 17021867624546731719913855)
    ·
      refine ⟨25532801436820097579870783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17021867624546731719913855 25532801436820097579870783)
      ·
        refine ⟨38299202155230146369806175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25532801436820097579870783 38299202155230146369806175)
        ·
          refine ⟨57448803232845219554709263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38299202155230146369806175 57448803232845219554709263)
          ·
            refine ⟨86173204849267829332063895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57448803232845219554709263 86173204849267829332063895)
            ·
              refine ⟨129259807273901743998095843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86173204849267829332063895 129259807273901743998095843)
              ·
                refine ⟨193889710910852615997143765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129259807273901743998095843 193889710910852615997143765)
                ·
                  refine ⟨4544290099473108187433057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 193889710910852615997143765 4544290099473108187433057)
                  ·
                    refine ⟨3408217574604831140574793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4544290099473108187433057 3408217574604831140574793)
                    ·
                      refine ⟨2556163180953623355431095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3408217574604831140574793 2556163180953623355431095)
                      ·
                        rfl

theorem cell23_4978110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2].length) (baseStart_4978110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4978110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4978110 prefixEnd_4978110 := by exact prefixLift 4978110
  have htrace : WordTrace (prefixWord ++ tailWord_4978110) baseStart_4978110 baseEnd_4978110 := by
    simpa [prefixWord, tailWord_4978110, baseEnd_4978110] using wordTrace_append hprefix tailTrace_4978110
  have hstable : (prefixWord ++ tailWord_4978110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4978110).length < 2 ^ (prefixWord ++ tailWord_4978110).sum := by decide
  have hdescent : baseEnd_4978110 < baseStart_4978110 := by decide
  rcases family_descends (prefixWord ++ tailWord_4978110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4978127 : List Nat := [1, 1, 2, 1, 1, 4, 4, 4, 1, 2, 2]
def baseStart_4978127 : Nat := 118140960795 + 4978127 * 2 ^ 59
def prefixEnd_4978127 : Nat := 4983230072969 + 3 ^ 40 * 4978127 * 2
def baseEnd_4978127 : Nat := 2556171910124749788918517

theorem tailTrace_4978127 : CollatzResearch.WordTrace tailWord_4978127 prefixEnd_4978127 2556171910124749788918517 := by
  unfold tailWord_4978127
  simp only [CollatzResearch.WordTrace]
  refine ⟨181567208036103550249116635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121044805357402366832744423 181567208036103550249116635)
  ·
    refine ⟨272350812054155325373674953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181567208036103550249116635 272350812054155325373674953)
    ·
      refine ⟨204263109040616494030256215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 272350812054155325373674953 204263109040616494030256215)
      ·
        refine ⟨306394663560924741045384323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204263109040616494030256215 306394663560924741045384323)
        ·
          refine ⟨459591995341387111568076485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 306394663560924741045384323 459591995341387111568076485)
          ·
            refine ⟨86173499126510083419014341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 459591995341387111568076485 86173499126510083419014341)
            ·
              refine ⟨16157531086220640641065189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86173499126510083419014341 16157531086220640641065189)
              ·
                refine ⟨3029537078666370120199723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16157531086220640641065189 3029537078666370120199723)
                ·
                  refine ⟨4544305617999555180299585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3029537078666370120199723 4544305617999555180299585)
                  ·
                    refine ⟨3408229213499666385224689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4544305617999555180299585 3408229213499666385224689)
                    ·
                      refine ⟨2556171910124749788918517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3408229213499666385224689 2556171910124749788918517)
                      ·
                        rfl

theorem cell23_4978127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 4, 1, 2, 2].length) (baseStart_4978127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4978127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4978127 prefixEnd_4978127 := by exact prefixLift 4978127
  have htrace : WordTrace (prefixWord ++ tailWord_4978127) baseStart_4978127 baseEnd_4978127 := by
    simpa [prefixWord, tailWord_4978127, baseEnd_4978127] using wordTrace_append hprefix tailTrace_4978127
  have hstable : (prefixWord ++ tailWord_4978127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4978127).length < 2 ^ (prefixWord ++ tailWord_4978127).sum := by decide
  have hdescent : baseEnd_4978127 < baseStart_4978127 := by decide
  rcases family_descends (prefixWord ++ tailWord_4978127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4978153 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 7, 3, 2]
def baseStart_4978153 : Nat := 118140960795 + 4978153 * 2 ^ 59
def prefixEnd_4978153 : Nat := 4983230072969 + 3 ^ 40 * 4978153 * 2
def baseEnd_4978153 : Nat := 2556185260621766687193397

theorem tailTrace_4978153 : CollatzResearch.WordTrace tailWord_4978153 prefixEnd_4978153 2556185260621766687193397 := by
  unfold tailWord_4978153
  simp only [CollatzResearch.WordTrace]
  refine ⟨181568156334009356689563113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121045437556006237793042075 181568156334009356689563113)
  ·
    refine ⟨136176117250507017517172335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181568156334009356689563113 136176117250507017517172335)
    ·
      refine ⟨204264175875760526275758503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136176117250507017517172335 204264175875760526275758503)
      ·
        refine ⟨306396263813640789413637755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204264175875760526275758503 306396263813640789413637755)
        ·
          refine ⟨459594395720461184120456633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 306396263813640789413637755 459594395720461184120456633)
          ·
            refine ⟨344695796790345888090342475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 459594395720461184120456633 344695796790345888090342475)
            ·
              refine ⟨517043695185518832135513713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 344695796790345888090342475 517043695185518832135513713)
              ·
                refine ⟨387782771389139124101635285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 517043695185518832135513713 387782771389139124101635285)
                ·
                  refine ⟨9088658704432948221132077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 387782771389139124101635285 9088658704432948221132077)
                  ·
                    refine ⟨3408247014162355582924529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9088658704432948221132077 3408247014162355582924529)
                    ·
                      refine ⟨2556185260621766687193397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3408247014162355582924529 2556185260621766687193397)
                      ·
                        rfl

theorem cell23_4978153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 7, 3, 2].length) (baseStart_4978153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4978153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4978153 prefixEnd_4978153 := by exact prefixLift 4978153
  have htrace : WordTrace (prefixWord ++ tailWord_4978153) baseStart_4978153 baseEnd_4978153 := by
    simpa [prefixWord, tailWord_4978153, baseEnd_4978153] using wordTrace_append hprefix tailTrace_4978153
  have hstable : (prefixWord ++ tailWord_4978153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4978153).length < 2 ^ (prefixWord ++ tailWord_4978153).sum := by decide
  have hdescent : baseEnd_4978153 < baseStart_4978153 := by decide
  rcases family_descends (prefixWord ++ tailWord_4978153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4978170 : List Nat := [3, 1, 1, 1, 1, 2, 3, 5, 1, 3, 2]
def baseStart_4978170 : Nat := 118140960795 + 4978170 * 2 ^ 59
def prefixEnd_4978170 : Nat := 4983230072969 + 3 ^ 40 * 4978170 * 2
def baseEnd_4978170 : Nat := 2556193989792893120680819

theorem tailTrace_4978170 : CollatzResearch.WordTrace tailWord_4978170 prefixEnd_4978170 2556193989792893120680819 := by
  unfold tailWord_4978170
  simp only [CollatzResearch.WordTrace]
  refine ⟨45392194093736942148232991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121045850916631845728621309 45392194093736942148232991)
  ·
    refine ⟨68088291140605413222349487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45392194093736942148232991 68088291140605413222349487)
    ·
      refine ⟨102132436710908119833524231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68088291140605413222349487 102132436710908119833524231)
      ·
        refine ⟨153198655066362179750286347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102132436710908119833524231 153198655066362179750286347)
        ·
          refine ⟨229797982599543269625429521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153198655066362179750286347 229797982599543269625429521)
          ·
            refine ⟨172348486949657452219072141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 229797982599543269625429521 172348486949657452219072141)
            ·
              refine ⟨64630682606121544582152053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 172348486949657452219072141 64630682606121544582152053)
              ·
                refine ⟨6059126494323894804576755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64630682606121544582152053 6059126494323894804576755)
                ·
                  refine ⟨9088689741485842206865133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6059126494323894804576755 9088689741485842206865133)
                  ·
                    refine ⟨3408258653057190827574425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9088689741485842206865133 3408258653057190827574425)
                    ·
                      refine ⟨2556193989792893120680819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3408258653057190827574425 2556193989792893120680819)
                      ·
                        rfl

theorem cell23_4978170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 5, 1, 3, 2].length) (baseStart_4978170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4978170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4978170 prefixEnd_4978170 := by exact prefixLift 4978170
  have htrace : WordTrace (prefixWord ++ tailWord_4978170) baseStart_4978170 baseEnd_4978170 := by
    simpa [prefixWord, tailWord_4978170, baseEnd_4978170] using wordTrace_append hprefix tailTrace_4978170
  have hstable : (prefixWord ++ tailWord_4978170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4978170).length < 2 ^ (prefixWord ++ tailWord_4978170).sum := by decide
  have hdescent : baseEnd_4978170 < baseStart_4978170 := by decide
  rcases family_descends (prefixWord ++ tailWord_4978170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4978178 : List Nat := [3, 4, 1, 2, 1, 2, 3, 2, 1, 2, 2]
def baseStart_4978178 : Nat := 118140960795 + 4978178 * 2 ^ 59
def prefixEnd_4978178 : Nat := 4983230072969 + 3 ^ 40 * 4978178 * 2
def baseEnd_4978178 : Nat := 2556198097638129089380783

theorem tailTrace_4978178 : CollatzResearch.WordTrace tailWord_4978178 prefixEnd_4978178 2556198097638129089380783 := by
  unfold tailWord_4978178
  simp only [CollatzResearch.WordTrace]
  refine ⟨45392267039729696489805797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121046045439279190639482125 45392267039729696489805797)
  ·
    refine ⟨8511050069949318091838587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45392267039729696489805797 8511050069949318091838587)
    ·
      refine ⟨12766575104923977137757881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8511050069949318091838587 12766575104923977137757881)
      ·
        refine ⟨9574931328692982853318411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12766575104923977137757881 9574931328692982853318411)
        ·
          refine ⟨14362396993039474279977617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9574931328692982853318411 14362396993039474279977617)
          ·
            refine ⟨10771797744779605709983213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14362396993039474279977617 10771797744779605709983213)
            ·
              refine ⟨4039424154292352141243705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10771797744779605709983213 4039424154292352141243705)
              ·
                refine ⟨3029568115719264105932779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4039424154292352141243705 3029568115719264105932779)
                ·
                  refine ⟨4544352173578896158899169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3029568115719264105932779 4544352173578896158899169)
                  ·
                    refine ⟨3408264130184172119174377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4544352173578896158899169 3408264130184172119174377)
                    ·
                      refine ⟨2556198097638129089380783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3408264130184172119174377 2556198097638129089380783)
                      ·
                        rfl

theorem cell23_4978178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_4978178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4978178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4978178 prefixEnd_4978178 := by exact prefixLift 4978178
  have htrace : WordTrace (prefixWord ++ tailWord_4978178) baseStart_4978178 baseEnd_4978178 := by
    simpa [prefixWord, tailWord_4978178, baseEnd_4978178] using wordTrace_append hprefix tailTrace_4978178
  have hstable : (prefixWord ++ tailWord_4978178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4978178).length < 2 ^ (prefixWord ++ tailWord_4978178).sum := by decide
  have hdescent : baseEnd_4978178 < baseStart_4978178 := by decide
  rcases family_descends (prefixWord ++ tailWord_4978178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4978260 : List Nat := [2, 4, 1, 1, 1, 2, 1, 2, 2, 5, 2]
def baseStart_4978260 : Nat := 118140960795 + 4978260 * 2 ^ 59
def prefixEnd_4978260 : Nat := 4983230072969 + 3 ^ 40 * 4978260 * 2
def baseEnd_4978260 : Nat := 2556240203051797768555405

theorem tailTrace_4978260 : CollatzResearch.WordTrace tailWord_4978260 prefixEnd_4978260 2556240203051797768555405 := by
  unfold tailWord_4978260
  simp only [CollatzResearch.WordTrace]
  refine ⟨90786029472310856981854117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121048039296414475975805489 90786029472310856981854117)
  ·
    refine ⟨17022380526058285684097647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90786029472310856981854117 17022380526058285684097647)
    ·
      refine ⟨25533570789087428526146471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17022380526058285684097647 25533570789087428526146471)
      ·
        refine ⟨38300356183631142789219707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25533570789087428526146471 38300356183631142789219707)
        ·
          refine ⟨57450534275446714183829561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38300356183631142789219707 57450534275446714183829561)
          ·
            refine ⟨43087900706585035637872171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57450534275446714183829561 43087900706585035637872171)
            ·
              refine ⟨64631851059877553456808257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43087900706585035637872171 64631851059877553456808257)
              ·
                refine ⟨48473888294908165092606193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64631851059877553456808257 48473888294908165092606193)
                ·
                  refine ⟨36355416221181123819454645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48473888294908165092606193 36355416221181123819454645)
                  ·
                    refine ⟨3408320270735730358073873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36355416221181123819454645 3408320270735730358073873)
                    ·
                      refine ⟨2556240203051797768555405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3408320270735730358073873 2556240203051797768555405)
                      ·
                        rfl

theorem cell23_4978260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 2, 5, 2].length) (baseStart_4978260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4978260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4978260 prefixEnd_4978260 := by exact prefixLift 4978260
  have htrace : WordTrace (prefixWord ++ tailWord_4978260) baseStart_4978260 baseEnd_4978260 := by
    simpa [prefixWord, tailWord_4978260, baseEnd_4978260] using wordTrace_append hprefix tailTrace_4978260
  have hstable : (prefixWord ++ tailWord_4978260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4978260).length < 2 ^ (prefixWord ++ tailWord_4978260).sum := by decide
  have hdescent : baseEnd_4978260 < baseStart_4978260 := by decide
  rcases family_descends (prefixWord ++ tailWord_4978260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4978273 : List Nat := [1, 2, 3, 1, 1, 3, 3, 1, 1, 3, 4]
def baseStart_4978273 : Nat := 118140960795 + 4978273 * 2 ^ 59
def prefixEnd_4978273 : Nat := 4983230072969 + 3 ^ 40 * 4978273 * 2
def baseEnd_4978273 : Nat := 2556246878300306217692845

theorem tailTrace_4978273 : CollatzResearch.WordTrace tailWord_4978273 prefixEnd_4978273 2556246878300306217692845 := by
  unfold tailWord_4978273
  simp only [CollatzResearch.WordTrace]
  refine ⟨181572533093574617183931473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121048355395716411455954315 181572533093574617183931473)
  ·
    refine ⟨136179399820180962887948605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181572533093574617183931473 136179399820180962887948605)
    ·
      refine ⟨51067274932567861082980727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136179399820180962887948605 51067274932567861082980727)
      ·
        refine ⟨76600912398851791624471091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51067274932567861082980727 76600912398851791624471091)
        ·
          refine ⟨114901368598277687436706637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76600912398851791624471091 114901368598277687436706637)
          ·
            refine ⟨43088013224354132788764989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114901368598277687436706637 43088013224354132788764989)
            ·
              refine ⟨16158004959132799795786871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43088013224354132788764989 16158004959132799795786871)
              ·
                refine ⟨24237007438699199693680307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16158004959132799795786871 24237007438699199693680307)
                ·
                  refine ⟨36355511158048799540520461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24237007438699199693680307 36355511158048799540520461)
                  ·
                    refine ⟨13633316684268299827695173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36355511158048799540520461 13633316684268299827695173)
                    ·
                      refine ⟨2556246878300306217692845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13633316684268299827695173 2556246878300306217692845)
                      ·
                        rfl

theorem cell23_4978273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_4978273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4978273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4978273 prefixEnd_4978273 := by exact prefixLift 4978273
  have htrace : WordTrace (prefixWord ++ tailWord_4978273) baseStart_4978273 baseEnd_4978273 := by
    simpa [prefixWord, tailWord_4978273, baseEnd_4978273] using wordTrace_append hprefix tailTrace_4978273
  have hstable : (prefixWord ++ tailWord_4978273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4978273).length < 2 ^ (prefixWord ++ tailWord_4978273).sum := by decide
  have hdescent : baseEnd_4978273 < baseStart_4978273 := by decide
  rcases family_descends (prefixWord ++ tailWord_4978273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4978313 : List Nat := [1, 2, 1, 1, 4, 1, 2, 5, 6]
def baseStart_4978313 : Nat := 118140960795 + 4978313 * 2 ^ 59
def prefixEnd_4978313 : Nat := 4983230072969 + 3 ^ 40 * 4978313 * 2
def baseEnd_4978313 : Nat := 284029713058498451243629

theorem tailTrace_4978313 : CollatzResearch.WordTrace tailWord_4978313 prefixEnd_4978313 284029713058498451243629 := by
  unfold tailWord_4978313
  simp only [CollatzResearch.WordTrace]
  refine ⟨181573992013429704015387593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121049328008953136010258395 181573992013429704015387593)
  ·
    refine ⟨136180494010072278011540695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181573992013429704015387593 136180494010072278011540695)
    ·
      refine ⟨204270741015108417017311043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136180494010072278011540695 204270741015108417017311043)
      ·
        refine ⟨306406111522662625525966565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204270741015108417017311043 306406111522662625525966565)
        ·
          refine ⟨57451145910499242286118731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 306406111522662625525966565 57451145910499242286118731)
          ·
            refine ⟨86176718865748863429178097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57451145910499242286118731 86176718865748863429178097)
            ·
              refine ⟨64632539149311647571883573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86176718865748863429178097 64632539149311647571883573)
              ·
                refine ⟨6059300545247966959864085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64632539149311647571883573 6059300545247966959864085)
                ·
                  refine ⟨284029713058498451243629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6059300545247966959864085 284029713058498451243629)
                  ·
                    rfl

theorem cell23_4978313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 5, 6].length) (baseStart_4978313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4978313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4978313 prefixEnd_4978313 := by exact prefixLift 4978313
  have htrace : WordTrace (prefixWord ++ tailWord_4978313) baseStart_4978313 baseEnd_4978313 := by
    simpa [prefixWord, tailWord_4978313, baseEnd_4978313] using wordTrace_append hprefix tailTrace_4978313
  have hstable : (prefixWord ++ tailWord_4978313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4978313).length < 2 ^ (prefixWord ++ tailWord_4978313).sum := by decide
  have hdescent : baseEnd_4978313 < baseStart_4978313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4978313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4978383 : List Nat := [1, 1, 2, 1, 1, 3, 1, 4, 3, 1, 5]
def baseStart_4978383 : Nat := 118140960795 + 4978383 * 2 ^ 59
def prefixEnd_4978383 : Nat := 4983230072969 + 3 ^ 40 * 4978383 * 2
def baseEnd_4978383 : Nat := 2556303361172300787317339

theorem tailTrace_4978383 : CollatzResearch.WordTrace tailWord_4978383 prefixEnd_4978383 2556303361172300787317339 := by
  unfold tailWord_4978383
  simp only [CollatzResearch.WordTrace]
  refine ⟨181576545123176105970435803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121051030082117403980290535 181576545123176105970435803)
  ·
    refine ⟨272364817684764158955653705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181576545123176105970435803 272364817684764158955653705)
    ·
      refine ⟨204273613263573119216740279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 272364817684764158955653705 204273613263573119216740279)
      ·
        refine ⟨306410419895359678825110419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204273613263573119216740279 306410419895359678825110419)
        ·
          refine ⟨459615629843039518237665629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 306410419895359678825110419 459615629843039518237665629)
          ·
            refine ⟨172355861191139819339124611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 459615629843039518237665629 172355861191139819339124611)
            ·
              refine ⟨258533791786709729008686917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172355861191139819339124611 258533791786709729008686917)
              ·
                refine ⟨48475085960008074189128797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 258533791786709729008686917 48475085960008074189128797)
                ·
                  refine ⟨18178157235003027820923299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48475085960008074189128797 18178157235003027820923299)
                  ·
                    refine ⟨27267235852504541731384949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18178157235003027820923299 27267235852504541731384949)
                    ·
                      refine ⟨2556303361172300787317339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27267235852504541731384949 2556303361172300787317339)
                      ·
                        rfl

theorem cell23_4978383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3, 1, 5].length) (baseStart_4978383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4978383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4978383 prefixEnd_4978383 := by exact prefixLift 4978383
  have htrace : WordTrace (prefixWord ++ tailWord_4978383) baseStart_4978383 baseEnd_4978383 := by
    simpa [prefixWord, tailWord_4978383, baseEnd_4978383] using wordTrace_append hprefix tailTrace_4978383
  have hstable : (prefixWord ++ tailWord_4978383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4978383).length < 2 ^ (prefixWord ++ tailWord_4978383).sum := by decide
  have hdescent : baseEnd_4978383 < baseStart_4978383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4978383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4978400 : List Nat := [2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 5]
def baseStart_4978400 : Nat := 118140960795 + 4978400 * 2 ^ 59
def prefixEnd_4978400 : Nat := 4983230072969 + 3 ^ 40 * 4978400 * 2
def baseEnd_4978400 : Nat := 2556312090343427220804761

theorem tailTrace_4978400 : CollatzResearch.WordTrace tailWord_4978400 prefixEnd_4978400 2556312090343427220804761 := by
  unfold tailWord_4978400
  simp only [CollatzResearch.WordTrace]
  refine ⟨90788582582057258936902327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121051443442743011915869769 90788582582057258936902327)
  ·
    refine ⟨136182873873085888405353491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90788582582057258936902327 136182873873085888405353491)
    ·
      refine ⟨204274310809628832608030237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136182873873085888405353491 204274310809628832608030237)
      ·
        refine ⟨76602866553610812228011339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 204274310809628832608030237 76602866553610812228011339)
        ·
          refine ⟨114904299830416218342017009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76602866553610812228011339 114904299830416218342017009)
          ·
            refine ⟨86178224872812163756512757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114904299830416218342017009 86178224872812163756512757)
            ·
              refine ⟨8079208581826140352173071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 86178224872812163756512757 8079208581826140352173071)
              ·
                refine ⟨12118812872739210528259607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8079208581826140352173071 12118812872739210528259607)
                ·
                  refine ⟨18178219309108815792389411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12118812872739210528259607 18178219309108815792389411)
                  ·
                    refine ⟨27267328963663223688584117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18178219309108815792389411 27267328963663223688584117)
                    ·
                      refine ⟨2556312090343427220804761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27267328963663223688584117 2556312090343427220804761)
                      ·
                        rfl

theorem cell23_4978400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 5].length) (baseStart_4978400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4978400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4978400 prefixEnd_4978400 := by exact prefixLift 4978400
  have htrace : WordTrace (prefixWord ++ tailWord_4978400) baseStart_4978400 baseEnd_4978400 := by
    simpa [prefixWord, tailWord_4978400, baseEnd_4978400] using wordTrace_append hprefix tailTrace_4978400
  have hstable : (prefixWord ++ tailWord_4978400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4978400).length < 2 ^ (prefixWord ++ tailWord_4978400).sum := by decide
  have hdescent : baseEnd_4978400 < baseStart_4978400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4978400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4978403 : List Nat := [1, 1, 1, 7, 13]
def baseStart_4978403 : Nat := 118140960795 + 4978403 * 2 ^ 59
def prefixEnd_4978403 : Nat := 4983230072969 + 3 ^ 40 * 4978403 * 2
def baseEnd_4978403 : Nat := 3506603060062264347143

theorem tailTrace_4978403 : CollatzResearch.WordTrace tailWord_4978403 prefixEnd_4978403 3506603060062264347143 := by
  unfold tailWord_4978403
  simp only [CollatzResearch.WordTrace]
  refine ⟨181577274583103649386163863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121051516388735766257442575 181577274583103649386163863)
  ·
    refine ⟨272365911874655474079245795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181577274583103649386163863 272365911874655474079245795)
    ·
      refine ⟨408548867811983211118868693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272365911874655474079245795 408548867811983211118868693)
      ·
        refine ⟨9575364089343356510598485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 408548867811983211118868693 9575364089343356510598485)
        ·
          refine ⟨3506603060062264347143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 9575364089343356510598485 3506603060062264347143)
          ·
            rfl

theorem cell23_4978403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 13].length) (baseStart_4978403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4978403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4978403 prefixEnd_4978403 := by exact prefixLift 4978403
  have htrace : WordTrace (prefixWord ++ tailWord_4978403) baseStart_4978403 baseEnd_4978403 := by
    simpa [prefixWord, tailWord_4978403, baseEnd_4978403] using wordTrace_append hprefix tailTrace_4978403
  have hstable : (prefixWord ++ tailWord_4978403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4978403).length < 2 ^ (prefixWord ++ tailWord_4978403).sum := by decide
  have hdescent : baseEnd_4978403 < baseStart_4978403 := by decide
  rcases family_descends (prefixWord ++ tailWord_4978403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4978408 : List Nat := [2, 1, 4, 1, 3, 3, 2, 2, 1, 1, 3]
def baseStart_4978408 : Nat := 118140960795 + 4978408 * 2 ^ 59
def prefixEnd_4978408 : Nat := 4983230072969 + 3 ^ 40 * 4978408 * 2
def baseEnd_4978408 : Nat := 2556316198188663189504725

theorem tailTrace_4978408 : CollatzResearch.WordTrace tailWord_4978408 prefixEnd_4978408 2556316198188663189504725 := by
  unfold tailWord_4978408
  simp only [CollatzResearch.WordTrace]
  refine ⟨90788728474042767620047939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121051637965390356826730585 90788728474042767620047939)
  ·
    refine ⟨136183092711064151430071909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90788728474042767620047939 136183092711064151430071909)
    ·
      refine ⟨25534329883324528393138483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 136183092711064151430071909 25534329883324528393138483)
      ·
        refine ⟨38301494824986792589707725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25534329883324528393138483 38301494824986792589707725)
        ·
          refine ⟨14363060559370047221140397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38301494824986792589707725 14363060559370047221140397)
          ·
            refine ⟨5386147709763767707927649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14363060559370047221140397 5386147709763767707927649)
            ·
              refine ⟨4039610782322825780945737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5386147709763767707927649 4039610782322825780945737)
              ·
                refine ⟨3029708086742119335709303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4039610782322825780945737 3029708086742119335709303)
                ·
                  refine ⟨4544562130113179003563955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3029708086742119335709303 4544562130113179003563955)
                  ·
                    refine ⟨6816843195169768505345933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4544562130113179003563955 6816843195169768505345933)
                    ·
                      refine ⟨2556316198188663189504725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6816843195169768505345933 2556316198188663189504725)
                      ·
                        rfl

theorem cell23_4978408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 2, 1, 1, 3].length) (baseStart_4978408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4978408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4978408 prefixEnd_4978408 := by exact prefixLift 4978408
  have htrace : WordTrace (prefixWord ++ tailWord_4978408) baseStart_4978408 baseEnd_4978408 := by
    simpa [prefixWord, tailWord_4978408, baseEnd_4978408] using wordTrace_append hprefix tailTrace_4978408
  have hstable : (prefixWord ++ tailWord_4978408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4978408).length < 2 ^ (prefixWord ++ tailWord_4978408).sum := by decide
  have hdescent : baseEnd_4978408 < baseStart_4978408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4978408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4978414 : List Nat := [4, 1, 2, 1, 1, 2, 2, 3, 3, 2, 2]
def baseStart_4978414 : Nat := 118140960795 + 4978414 * 2 ^ 59
def prefixEnd_4978414 : Nat := 4983230072969 + 3 ^ 40 * 4978414 * 2
def baseEnd_4978414 : Nat := 2556319279072590166029697

theorem tailTrace_4978414 : CollatzResearch.WordTrace tailWord_4978414 prefixEnd_4978414 2556319279072590166029697 := by
  unfold tailWord_4978414
  simp only [CollatzResearch.WordTrace]
  refine ⟨22697209473257974783101787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121051783857375865509876197 22697209473257974783101787)
  ·
    refine ⟨34045814209886962174652681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22697209473257974783101787 34045814209886962174652681)
    ·
      refine ⟨25534360657415221630989511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34045814209886962174652681 25534360657415221630989511)
      ·
        refine ⟨38301540986122832446484267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25534360657415221630989511 38301540986122832446484267)
        ·
          refine ⟨57452311479184248669726401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38301540986122832446484267 57452311479184248669726401)
          ·
            refine ⟨43089233609388186502294801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57452311479184248669726401 43089233609388186502294801)
            ·
              refine ⟨32316925207041139876721101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43089233609388186502294801 32316925207041139876721101)
              ·
                refine ⟨12118846952640427453770413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32316925207041139876721101 12118846952640427453770413)
                ·
                  refine ⟨4544567607240160295163905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12118846952640427453770413 4544567607240160295163905)
                  ·
                    refine ⟨3408425705430120221372929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4544567607240160295163905 3408425705430120221372929)
                    ·
                      refine ⟨2556319279072590166029697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3408425705430120221372929 2556319279072590166029697)
                      ·
                        rfl

theorem cell23_4978414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3, 3, 2, 2].length) (baseStart_4978414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4978414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4978414 prefixEnd_4978414 := by exact prefixLift 4978414
  have htrace : WordTrace (prefixWord ++ tailWord_4978414) baseStart_4978414 baseEnd_4978414 := by
    simpa [prefixWord, tailWord_4978414, baseEnd_4978414] using wordTrace_append hprefix tailTrace_4978414
  have hstable : (prefixWord ++ tailWord_4978414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4978414).length < 2 ^ (prefixWord ++ tailWord_4978414).sum := by decide
  have hdescent : baseEnd_4978414 < baseStart_4978414 := by decide
  rcases family_descends (prefixWord ++ tailWord_4978414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4978423 : List Nat := [1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 6]
def baseStart_4978423 : Nat := 118140960795 + 4978423 * 2 ^ 59
def prefixEnd_4978423 : Nat := 4983230072969 + 3 ^ 40 * 4978423 * 2
def baseEnd_4978423 : Nat := 2556323900398480630817155

theorem tailTrace_4978423 : CollatzResearch.WordTrace tailWord_4978423 prefixEnd_4978423 2556323900398480630817155 := by
  unfold tailWord_4978423
  simp only [CollatzResearch.WordTrace]
  refine ⟨181578004043031192801891923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121052002695354128534594615 181578004043031192801891923)
  ·
    refine ⟨272367006064546789202837885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181578004043031192801891923 272367006064546789202837885)
    ·
      refine ⟨102137627274205045951064207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 272367006064546789202837885 102137627274205045951064207)
      ·
        refine ⟨153206440911307568926596311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102137627274205045951064207 153206440911307568926596311)
        ·
          refine ⟨229809661366961353389894467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153206440911307568926596311 229809661366961353389894467)
          ·
            refine ⟨344714492050442030084841701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229809661366961353389894467 344714492050442030084841701)
            ·
              refine ⟨64633967259457880640907819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 344714492050442030084841701 64633967259457880640907819)
              ·
                refine ⟨96950950889186820961361729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64633967259457880640907819 96950950889186820961361729)
                ·
                  refine ⟨72713213166890115721021297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 96950950889186820961361729 72713213166890115721021297)
                  ·
                    refine ⟨54534909875167586790765973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 72713213166890115721021297 54534909875167586790765973)
                    ·
                      refine ⟨2556323900398480630817155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54534909875167586790765973 2556323900398480630817155)
                      ·
                        rfl

theorem cell23_4978423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 6].length) (baseStart_4978423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4978423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4978423 prefixEnd_4978423 := by exact prefixLift 4978423
  have htrace : WordTrace (prefixWord ++ tailWord_4978423) baseStart_4978423 baseEnd_4978423 := by
    simpa [prefixWord, tailWord_4978423, baseEnd_4978423] using wordTrace_append hprefix tailTrace_4978423
  have hstable : (prefixWord ++ tailWord_4978423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4978423).length < 2 ^ (prefixWord ++ tailWord_4978423).sum := by decide
  have hdescent : baseEnd_4978423 < baseStart_4978423 := by decide
  rcases family_descends (prefixWord ++ tailWord_4978423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4978434 : List Nat := [3, 4, 1, 1, 1, 1, 2, 4, 1, 2, 3]
def baseStart_4978434 : Nat := 118140960795 + 4978434 * 2 ^ 59
def prefixEnd_4978434 : Nat := 4983230072969 + 3 ^ 40 * 4978434 * 2
def baseEnd_4978434 : Nat := 2556329548685680087779605

theorem tailTrace_4978434 : CollatzResearch.WordTrace tailWord_4978434 prefixEnd_4978434 2556329548685680087779605 := by
  unfold tailWord_4978434
  simp only [CollatzResearch.WordTrace]
  refine ⟨45394601311497835420135589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121052270163994227787028237 45394601311497835420135589)
  ·
    refine ⟨8511487745905844141275423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45394601311497835420135589 8511487745905844141275423)
    ·
      refine ⟨12767231618858766211913135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8511487745905844141275423 12767231618858766211913135)
      ·
        refine ⟨19150847428288149317869703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12767231618858766211913135 19150847428288149317869703)
        ·
          refine ⟨28726271142432223976804555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19150847428288149317869703 28726271142432223976804555)
          ·
            refine ⟨43089406713648335965206833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28726271142432223976804555 43089406713648335965206833)
            ·
              refine ⟨32317055035236251973905125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43089406713648335965206833 32317055035236251973905125)
              ·
                refine ⟨6059447819106797245107211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32317055035236251973905125 6059447819106797245107211)
                ·
                  refine ⟨9089171728660195867660817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6059447819106797245107211 9089171728660195867660817)
                  ·
                    refine ⟨6816878796495146900745613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9089171728660195867660817 6816878796495146900745613)
                    ·
                      refine ⟨2556329548685680087779605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6816878796495146900745613 2556329548685680087779605)
                      ·
                        rfl

theorem cell23_4978434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_4978434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4978434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4978434 prefixEnd_4978434 := by exact prefixLift 4978434
  have htrace : WordTrace (prefixWord ++ tailWord_4978434) baseStart_4978434 baseEnd_4978434 := by
    simpa [prefixWord, tailWord_4978434, baseEnd_4978434] using wordTrace_append hprefix tailTrace_4978434
  have hstable : (prefixWord ++ tailWord_4978434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4978434).length < 2 ^ (prefixWord ++ tailWord_4978434).sum := by decide
  have hdescent : baseEnd_4978434 < baseStart_4978434 := by decide
  rcases family_descends (prefixWord ++ tailWord_4978434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4978481 : List Nat := [1, 2, 2, 3, 2, 3, 3, 1, 2, 1, 3]
def baseStart_4978481 : Nat := 118140960795 + 4978481 * 2 ^ 59
def prefixEnd_4978481 : Nat := 4983230072969 + 3 ^ 40 * 4978481 * 2
def baseEnd_4978481 : Nat := 2556353682276441403891889

theorem tailTrace_4978481 : CollatzResearch.WordTrace tailWord_4978481 prefixEnd_4978481 2556353682276441403891889 := by
  unfold tailWord_4978481
  simp only [CollatzResearch.WordTrace]
  refine ⟨181580119476821068707503297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121053412984547379138335531 181580119476821068707503297)
  ·
    refine ⟨136185089607615801530627473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181580119476821068707503297 136185089607615801530627473)
    ·
      refine ⟨102138817205711851147970605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136185089607615801530627473 102138817205711851147970605)
      ·
        refine ⟨38302056452141944180488977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102138817205711851147970605 38302056452141944180488977)
        ·
          refine ⟨28726542339106458135366733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38302056452141944180488977 28726542339106458135366733)
          ·
            refine ⟨10772453377164921800762525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28726542339106458135366733 10772453377164921800762525)
            ·
              refine ⟨4039670016436845675285947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10772453377164921800762525 4039670016436845675285947)
              ·
                refine ⟨6059505024655268512928921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4039670016436845675285947 6059505024655268512928921)
                ·
                  refine ⟨4544628768491451384696691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6059505024655268512928921 4544628768491451384696691)
                  ·
                    refine ⟨6816943152737177077045037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4544628768491451384696691 6816943152737177077045037)
                    ·
                      refine ⟨2556353682276441403891889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6816943152737177077045037 2556353682276441403891889)
                      ·
                        rfl

theorem cell23_4978481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 1, 2, 1, 3].length) (baseStart_4978481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4978481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4978481 prefixEnd_4978481 := by exact prefixLift 4978481
  have htrace : WordTrace (prefixWord ++ tailWord_4978481) baseStart_4978481 baseEnd_4978481 := by
    simpa [prefixWord, tailWord_4978481, baseEnd_4978481] using wordTrace_append hprefix tailTrace_4978481
  have hstable : (prefixWord ++ tailWord_4978481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4978481).length < 2 ^ (prefixWord ++ tailWord_4978481).sum := by decide
  have hdescent : baseEnd_4978481 < baseStart_4978481 := by decide
  rcases family_descends (prefixWord ++ tailWord_4978481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4978487 : List Nat := [1, 1, 3, 1, 2, 1, 2, 5, 1, 4, 2]
def baseStart_4978487 : Nat := 118140960795 + 4978487 * 2 ^ 59
def prefixEnd_4978487 : Nat := 4983230072969 + 3 ^ 40 * 4978487 * 2
def baseEnd_4978487 : Nat := 2556356763160368380416861

theorem tailTrace_4978487 : CollatzResearch.WordTrace tailWord_4978487 prefixEnd_4978487 2556356763160368380416861 := by
  unfold tailWord_4978487
  simp only [CollatzResearch.WordTrace]
  refine ⟨181580338314799331732221715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121053558876532887821481143 181580338314799331732221715)
  ·
    refine ⟨272370507472198997598332573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181580338314799331732221715 272370507472198997598332573)
    ·
      refine ⟨102138940302074624099374715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 272370507472198997598332573 102138940302074624099374715)
      ·
        refine ⟨153208410453111936149062073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102138940302074624099374715 153208410453111936149062073)
        ·
          refine ⟨114906307839833952111796555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153208410453111936149062073 114906307839833952111796555)
          ·
            refine ⟨172359461759750928167694833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114906307839833952111796555 172359461759750928167694833)
            ·
              refine ⟨129269596319813196125771125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 172359461759750928167694833 129269596319813196125771125)
              ·
                refine ⟨12119024654982487136791043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 129269596319813196125771125 12119024654982487136791043)
                ·
                  refine ⟨18178536982473730705186565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12119024654982487136791043 18178536982473730705186565)
                  ·
                    refine ⟨3408475684213824507222481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18178536982473730705186565 3408475684213824507222481)
                    ·
                      refine ⟨2556356763160368380416861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3408475684213824507222481 2556356763160368380416861)
                      ·
                        rfl

theorem cell23_4978487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5, 1, 4, 2].length) (baseStart_4978487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4978487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4978487 prefixEnd_4978487 := by exact prefixLift 4978487
  have htrace : WordTrace (prefixWord ++ tailWord_4978487) baseStart_4978487 baseEnd_4978487 := by
    simpa [prefixWord, tailWord_4978487, baseEnd_4978487] using wordTrace_append hprefix tailTrace_4978487
  have hstable : (prefixWord ++ tailWord_4978487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4978487).length < 2 ^ (prefixWord ++ tailWord_4978487).sum := by decide
  have hdescent : baseEnd_4978487 < baseStart_4978487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4978487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4978504 : List Nat := [2, 1, 3, 1, 1, 4, 1, 2, 4, 2, 2]
def baseStart_4978504 : Nat := 118140960795 + 4978504 * 2 ^ 59
def prefixEnd_4978504 : Nat := 4983230072969 + 3 ^ 40 * 4978504 * 2
def baseEnd_4978504 : Nat := 2556365492331494813904283

theorem tailTrace_4978504 : CollatzResearch.WordTrace tailWord_4978504 prefixEnd_4978504 2556365492331494813904283 := by
  unfold tailWord_4978504
  simp only [CollatzResearch.WordTrace]
  refine ⟨90790479177868871817795283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121053972237158495757060377 90790479177868871817795283)
  ·
    refine ⟨136185718766803307726692925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90790479177868871817795283 136185718766803307726692925)
    ·
      refine ⟨51069644537551240397509847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136185718766803307726692925 51069644537551240397509847)
      ·
        refine ⟨76604466806326860596264771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51069644537551240397509847 76604466806326860596264771)
        ·
          refine ⟨114906700209490290894397157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76604466806326860596264771 114906700209490290894397157)
          ·
            refine ⟨21545006289279429542699467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 114906700209490290894397157 21545006289279429542699467)
            ·
              refine ⟨32317509433919144314049201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21545006289279429542699467 32317509433919144314049201)
              ·
                refine ⟨24238132075439358235536901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32317509433919144314049201 24238132075439358235536901)
                ·
                  refine ⟨4544649764144879669163169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24238132075439358235536901 4544649764144879669163169)
                  ·
                    refine ⟨3408487323108659751872377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4544649764144879669163169 3408487323108659751872377)
                    ·
                      refine ⟨2556365492331494813904283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3408487323108659751872377 2556365492331494813904283)
                      ·
                        rfl

theorem cell23_4978504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 4, 2, 2].length) (baseStart_4978504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4978504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4978504 prefixEnd_4978504 := by exact prefixLift 4978504
  have htrace : WordTrace (prefixWord ++ tailWord_4978504) baseStart_4978504 baseEnd_4978504 := by
    simpa [prefixWord, tailWord_4978504, baseEnd_4978504] using wordTrace_append hprefix tailTrace_4978504
  have hstable : (prefixWord ++ tailWord_4978504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4978504).length < 2 ^ (prefixWord ++ tailWord_4978504).sum := by decide
  have hdescent : baseEnd_4978504 < baseStart_4978504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4978504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4978527 : List Nat := [1, 1, 2, 3, 1, 6, 1, 1, 7]
def baseStart_4978527 : Nat := 118140960795 + 4978527 * 2 ^ 59
def prefixEnd_4978527 : Nat := 4983230072969 + 3 ^ 40 * 4978527 * 2
def baseEnd_4978527 : Nat := 284041922487394247101853

theorem tailTrace_4978527 : CollatzResearch.WordTrace tailWord_4978527 prefixEnd_4978527 284041922487394247101853 := by
  unfold tailWord_4978527
  simp only [CollatzResearch.WordTrace]
  refine ⟨181581797234654418563677835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121054531489769612375785223 181581797234654418563677835)
  ·
    refine ⟨272372695851981627845516753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181581797234654418563677835 272372695851981627845516753)
    ·
      refine ⟨204279521888986220884137565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 272372695851981627845516753 204279521888986220884137565)
      ·
        refine ⟨76604820708369832831551587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 204279521888986220884137565 76604820708369832831551587)
        ·
          refine ⟨114907231062554749247327381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76604820708369832831551587 114907231062554749247327381)
          ·
            refine ⟨5386276456057253870968471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 114907231062554749247327381 5386276456057253870968471)
            ·
              refine ⟨8079414684085880806452707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5386276456057253870968471 8079414684085880806452707)
              ·
                refine ⟨12119122026128821209679061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8079414684085880806452707 12119122026128821209679061)
                ·
                  refine ⟨284041922487394247101853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12119122026128821209679061 284041922487394247101853)
                  ·
                    rfl

theorem cell23_4978527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 1, 7].length) (baseStart_4978527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4978527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4978527 prefixEnd_4978527 := by exact prefixLift 4978527
  have htrace : WordTrace (prefixWord ++ tailWord_4978527) baseStart_4978527 baseEnd_4978527 := by
    simpa [prefixWord, tailWord_4978527, baseEnd_4978527] using wordTrace_append hprefix tailTrace_4978527
  have hstable : (prefixWord ++ tailWord_4978527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4978527).length < 2 ^ (prefixWord ++ tailWord_4978527).sum := by decide
  have hdescent : baseEnd_4978527 < baseStart_4978527 := by decide
  rcases family_descends (prefixWord ++ tailWord_4978527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4978577 : List Nat := [1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 4]
def baseStart_4978577 : Nat := 118140960795 + 4978577 * 2 ^ 59
def prefixEnd_4978577 : Nat := 4983230072969 + 3 ^ 40 * 4978577 * 2
def baseEnd_4978577 : Nat := 2556402976419273028291447

theorem tailTrace_4978577 : CollatzResearch.WordTrace tailWord_4978577 prefixEnd_4978577 2556402976419273028291447 := by
  unfold tailWord_4978577
  simp only [CollatzResearch.WordTrace]
  refine ⟨181583620884473277102997985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121055747256315518068665323 181583620884473277102997985)
  ·
    refine ⟨136187715663354957827248489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181583620884473277102997985 136187715663354957827248489)
    ·
      refine ⟨102140786747516218370436367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136187715663354957827248489 102140786747516218370436367)
      ·
        refine ⟨153211180121274327555654551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102140786747516218370436367 153211180121274327555654551)
        ·
          refine ⟨229816770181911491333481827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153211180121274327555654551 229816770181911491333481827)
          ·
            refine ⟨344725155272867237000222741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229816770181911491333481827 344725155272867237000222741)
            ·
              refine ⟨16158991653415651734385441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 344725155272867237000222741 16158991653415651734385441)
              ·
                refine ⟨12119243740061738800789081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16158991653415651734385441 12119243740061738800789081)
                ·
                  refine ⟨9089432805046304100591811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12119243740061738800789081 9089432805046304100591811)
                  ·
                    refine ⟨13634149207569456150887717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9089432805046304100591811 13634149207569456150887717)
                    ·
                      refine ⟨2556402976419273028291447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13634149207569456150887717 2556402976419273028291447)
                      ·
                        rfl

theorem cell23_4978577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 4].length) (baseStart_4978577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4978577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4978577 prefixEnd_4978577 := by exact prefixLift 4978577
  have htrace : WordTrace (prefixWord ++ tailWord_4978577) baseStart_4978577 baseEnd_4978577 := by
    simpa [prefixWord, tailWord_4978577, baseEnd_4978577] using wordTrace_append hprefix tailTrace_4978577
  have hstable : (prefixWord ++ tailWord_4978577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4978577).length < 2 ^ (prefixWord ++ tailWord_4978577).sum := by decide
  have hdescent : baseEnd_4978577 < baseStart_4978577 := by decide
  rcases family_descends (prefixWord ++ tailWord_4978577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4978578 : List Nat := [3, 2, 3, 2, 1, 3, 2, 2, 5]
def baseStart_4978578 : Nat := 118140960795 + 4978578 * 2 ^ 59
def prefixEnd_4978578 : Nat := 4983230072969 + 3 ^ 40 * 4978578 * 2
def baseEnd_4978578 : Nat := 284044832211103058264327

theorem tailTrace_4978578 : CollatzResearch.WordTrace tailWord_4978578 prefixEnd_4978578 284044832211103058264327 := by
  unfold tailWord_4978578
  simp only [CollatzResearch.WordTrace]
  refine ⟨45395914339367413568446097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121055771571646436182522925 45395914339367413568446097)
  ·
    refine ⟨34046935754525560176334573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45395914339367413568446097 34046935754525560176334573)
    ·
      refine ⟨12767600907947085066125465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34046935754525560176334573 12767600907947085066125465)
      ·
        refine ⟨9575700680960313799594099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12767600907947085066125465 9575700680960313799594099)
        ·
          refine ⟨14363551021440470699391149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9575700680960313799594099 14363551021440470699391149)
          ·
            refine ⟨5386331633040176512271681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14363551021440470699391149 5386331633040176512271681)
            ·
              refine ⟨4039748724780132384203761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5386331633040176512271681 4039748724780132384203761)
              ·
                refine ⟨3029811543585099288152821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4039748724780132384203761 3029811543585099288152821)
                ·
                  refine ⟨284044832211103058264327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3029811543585099288152821 284044832211103058264327)
                  ·
                    rfl

theorem cell23_4978578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 2, 5].length) (baseStart_4978578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4978578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4978578 prefixEnd_4978578 := by exact prefixLift 4978578
  have htrace : WordTrace (prefixWord ++ tailWord_4978578) baseStart_4978578 baseEnd_4978578 := by
    simpa [prefixWord, tailWord_4978578, baseEnd_4978578] using wordTrace_append hprefix tailTrace_4978578
  have hstable : (prefixWord ++ tailWord_4978578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4978578).length < 2 ^ (prefixWord ++ tailWord_4978578).sum := by decide
  have hdescent : baseEnd_4978578 < baseStart_4978578 := by decide
  rcases family_descends (prefixWord ++ tailWord_4978578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4978597 : List Nat := [1, 3, 1, 2, 1, 1, 1, 4, 4, 2, 3]
def baseStart_4978597 : Nat := 118140960795 + 4978597 * 2 ^ 59
def prefixEnd_4978597 : Nat := 4983230072969 + 3 ^ 40 * 4978597 * 2
def baseEnd_4978597 : Nat := 2556413246032362950041355

theorem tailTrace_4978597 : CollatzResearch.WordTrace tailWord_4978597 prefixEnd_4978597 2556413246032362950041355 := by
  unfold tailWord_4978597
  simp only [CollatzResearch.WordTrace]
  refine ⟨181584350344400820518726045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121056233562933880345817363 181584350344400820518726045)
  ·
    refine ⟨68094131379150307694522267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181584350344400820518726045 68094131379150307694522267)
    ·
      refine ⟨102141197068725461541783401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68094131379150307694522267 102141197068725461541783401)
      ·
        refine ⟨76605897801544096156337551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102141197068725461541783401 76605897801544096156337551)
        ·
          refine ⟨114908846702316144234506327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76605897801544096156337551 114908846702316144234506327)
          ·
            refine ⟨172363270053474216351759491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114908846702316144234506327 172363270053474216351759491)
            ·
              refine ⟨258544905080211324527639237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172363270053474216351759491 258544905080211324527639237)
              ·
                refine ⟨48477169702539623348932357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 258544905080211324527639237 48477169702539623348932357)
                ·
                  refine ⟨9089469319226179377924817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48477169702539623348932357 9089469319226179377924817)
                  ·
                    refine ⟨6817101989419634533443613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9089469319226179377924817 6817101989419634533443613)
                    ·
                      refine ⟨2556413246032362950041355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6817101989419634533443613 2556413246032362950041355)
                      ·
                        rfl

theorem cell23_4978597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 4, 2, 3].length) (baseStart_4978597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4978597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4978597 prefixEnd_4978597 := by exact prefixLift 4978597
  have htrace : WordTrace (prefixWord ++ tailWord_4978597) baseStart_4978597 baseEnd_4978597 := by
    simpa [prefixWord, tailWord_4978597, baseEnd_4978597] using wordTrace_append hprefix tailTrace_4978597
  have hstable : (prefixWord ++ tailWord_4978597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4978597).length < 2 ^ (prefixWord ++ tailWord_4978597).sum := by decide
  have hdescent : baseEnd_4978597 < baseStart_4978597 := by decide
  rcases family_descends (prefixWord ++ tailWord_4978597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4978621 : List Nat := [1, 4, 1, 2, 3, 1, 1, 5, 1, 4]
def baseStart_4978621 : Nat := 118140960795 + 4978621 * 2 ^ 59
def prefixEnd_4978621 : Nat := 4983230072969 + 3 ^ 40 * 4978621 * 2
def baseEnd_4978621 : Nat := 852141856522690285380415

theorem tailTrace_4978621 : CollatzResearch.WordTrace tailWord_4978621 prefixEnd_4978621 852141856522690285380415 := by
  unfold tailWord_4978621
  simp only [CollatzResearch.WordTrace]
  refine ⟨181585225696313872617599717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121056817130875915078399811 181585225696313872617599717)
  ·
    refine ⟨34047229818058851115799947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 181585225696313872617599717 34047229818058851115799947)
    ·
      refine ⟨51070844727088276673699921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34047229818058851115799947 51070844727088276673699921)
      ·
        refine ⟨38303133545316207505274941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51070844727088276673699921 38303133545316207505274941)
        ·
          refine ⟨14363675079493577814478103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38303133545316207505274941 14363675079493577814478103)
          ·
            refine ⟨21545512619240366721717155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14363675079493577814478103 21545512619240366721717155)
            ·
              refine ⟨32318268928860550082575733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21545512619240366721717155 32318268928860550082575733)
              ·
                refine ⟨3029837712080676570241475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32318268928860550082575733 3029837712080676570241475)
                ·
                  refine ⟨4544756568121014855362213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3029837712080676570241475 4544756568121014855362213)
                  ·
                    refine ⟨852141856522690285380415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4544756568121014855362213 852141856522690285380415)
                    ·
                      rfl

theorem cell23_4978621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 5, 1, 4].length) (baseStart_4978621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4978621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4978621 prefixEnd_4978621 := by exact prefixLift 4978621
  have htrace : WordTrace (prefixWord ++ tailWord_4978621) baseStart_4978621 baseEnd_4978621 := by
    simpa [prefixWord, tailWord_4978621, baseEnd_4978621] using wordTrace_append hprefix tailTrace_4978621
  have hstable : (prefixWord ++ tailWord_4978621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4978621).length < 2 ^ (prefixWord ++ tailWord_4978621).sum := by decide
  have hdescent : baseEnd_4978621 < baseStart_4978621 := by decide
  rcases family_descends (prefixWord ++ tailWord_4978621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4978667 : List Nat := [1, 1, 1, 1, 2, 3, 1, 5, 3, 1, 4]
def baseStart_4978667 : Nat := 118140960795 + 4978667 * 2 ^ 59
def prefixEnd_4978667 : Nat := 4983230072969 + 3 ^ 40 * 4978667 * 2
def baseEnd_4978667 : Nat := 2556449189678177676166033

theorem tailTrace_4978667 : CollatzResearch.WordTrace tailWord_4978667 prefixEnd_4978667 2556449189678177676166033 := by
  unfold tailWord_4978667
  simp only [CollatzResearch.WordTrace]
  refine ⟨181586903454147222473774255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121057935636098148315849503 181586903454147222473774255)
  ·
    refine ⟨272380355181220833710661383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181586903454147222473774255 272380355181220833710661383)
    ·
      refine ⟨408570532771831250565992075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272380355181220833710661383 408570532771831250565992075)
      ·
        refine ⟨612855799157746875848988113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 408570532771831250565992075 612855799157746875848988113)
        ·
          refine ⟨459641849368310156886741085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 612855799157746875848988113 459641849368310156886741085)
          ·
            refine ⟨172365693513116308832527907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 459641849368310156886741085 172365693513116308832527907)
            ·
              refine ⟨258548540269674463248791861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172365693513116308832527907 258548540269674463248791861)
              ·
                refine ⟨24238925650281980929574237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 258548540269674463248791861 24238925650281980929574237)
                ·
                  refine ⟨9089597118855742848590339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24238925650281980929574237 9089597118855742848590339)
                  ·
                    refine ⟨13634395678283614272885509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9089597118855742848590339 13634395678283614272885509)
                    ·
                      refine ⟨2556449189678177676166033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13634395678283614272885509 2556449189678177676166033)
                      ·
                        rfl

theorem cell23_4978667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 3, 1, 4].length) (baseStart_4978667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4978667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4978667 prefixEnd_4978667 := by exact prefixLift 4978667
  have htrace : WordTrace (prefixWord ++ tailWord_4978667) baseStart_4978667 baseEnd_4978667 := by
    simpa [prefixWord, tailWord_4978667, baseEnd_4978667] using wordTrace_append hprefix tailTrace_4978667
  have hstable : (prefixWord ++ tailWord_4978667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4978667).length < 2 ^ (prefixWord ++ tailWord_4978667).sum := by decide
  have hdescent : baseEnd_4978667 < baseStart_4978667 := by decide
  rcases family_descends (prefixWord ++ tailWord_4978667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4978684 : List Nat := [2, 2, 2, 1, 2, 2, 1, 5, 1, 1, 4]
def baseStart_4978684 : Nat := 118140960795 + 4978684 * 2 ^ 59
def prefixEnd_4978684 : Nat := 4983230072969 + 3 ^ 40 * 4978684 * 2
def baseEnd_4978684 : Nat := 2556457918849304109653455

theorem tailTrace_4978684 : CollatzResearch.WordTrace tailWord_4978684 prefixEnd_4978684 2556457918849304109653455 := by
  unfold tailWord_4978684
  simp only [CollatzResearch.WordTrace]
  refine ⟨90793761747542817188571553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121058348996723756251428737 90793761747542817188571553)
  ·
    refine ⟨68095321310657112891428665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90793761747542817188571553 68095321310657112891428665)
    ·
      refine ⟨51071490982992834668571499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68095321310657112891428665 51071490982992834668571499)
      ·
        refine ⟨76607236474489252002857249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51071490982992834668571499 76607236474489252002857249)
        ·
          refine ⟨57455427355866939002142937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76607236474489252002857249 57455427355866939002142937)
          ·
            refine ⟨43091570516900204251607203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57455427355866939002142937 43091570516900204251607203)
            ·
              refine ⟨64637355775350306377410805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43091570516900204251607203 64637355775350306377410805)
              ·
                refine ⟨6059752103939091222882263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64637355775350306377410805 6059752103939091222882263)
                ·
                  refine ⟨9089628155908636834323395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6059752103939091222882263 9089628155908636834323395)
                  ·
                    refine ⟨13634442233862955251485093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9089628155908636834323395 13634442233862955251485093)
                    ·
                      refine ⟨2556457918849304109653455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13634442233862955251485093 2556457918849304109653455)
                      ·
                        rfl

theorem cell23_4978684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 5, 1, 1, 4].length) (baseStart_4978684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4978684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4978684 prefixEnd_4978684 := by exact prefixLift 4978684
  have htrace : WordTrace (prefixWord ++ tailWord_4978684) baseStart_4978684 baseEnd_4978684 := by
    simpa [prefixWord, tailWord_4978684, baseEnd_4978684] using wordTrace_append hprefix tailTrace_4978684
  have hstable : (prefixWord ++ tailWord_4978684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4978684).length < 2 ^ (prefixWord ++ tailWord_4978684).sum := by decide
  have hdescent : baseEnd_4978684 < baseStart_4978684 := by decide
  rcases family_descends (prefixWord ++ tailWord_4978684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4978695 : List Nat := [1, 1, 4, 3, 1, 3, 3, 2, 1, 1, 3]
def baseStart_4978695 : Nat := 118140960795 + 4978695 * 2 ^ 59
def prefixEnd_4978695 : Nat := 4983230072969 + 3 ^ 40 * 4978695 * 2
def baseEnd_4978695 : Nat := 2556463567136503566615905

theorem tailTrace_4978695 : CollatzResearch.WordTrace tailWord_4978695 prefixEnd_4978695 2556463567136503566615905 := by
  unfold tailWord_4978695
  simp only [CollatzResearch.WordTrace]
  refine ⟨181587924698045783255793539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121058616465363855503862359 181587924698045783255793539)
  ·
    refine ⟨272381887047068674883690309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181587924698045783255793539 272381887047068674883690309)
    ·
      refine ⟨51071603821325376540691933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 272381887047068674883690309 51071603821325376540691933)
      ·
        refine ⟨19151851432997016202759475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51071603821325376540691933 19151851432997016202759475)
        ·
          refine ⟨28727777149495524304139213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19151851432997016202759475 28727777149495524304139213)
          ·
            refine ⟨10772916431060821614052205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28727777149495524304139213 10772916431060821614052205)
            ·
              refine ⟨4039843661647808105269577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10772916431060821614052205 4039843661647808105269577)
              ·
                refine ⟨3029882746235856078952183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4039843661647808105269577 3029882746235856078952183)
                ·
                  refine ⟨4544824119353784118428275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3029882746235856078952183 4544824119353784118428275)
                  ·
                    refine ⟨6817236179030676177642413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4544824119353784118428275 6817236179030676177642413)
                    ·
                      refine ⟨2556463567136503566615905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6817236179030676177642413 2556463567136503566615905)
                      ·
                        rfl

theorem cell23_4978695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_4978695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4978695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4978695 prefixEnd_4978695 := by exact prefixLift 4978695
  have htrace : WordTrace (prefixWord ++ tailWord_4978695) baseStart_4978695 baseEnd_4978695 := by
    simpa [prefixWord, tailWord_4978695, baseEnd_4978695] using wordTrace_append hprefix tailTrace_4978695
  have hstable : (prefixWord ++ tailWord_4978695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4978695).length < 2 ^ (prefixWord ++ tailWord_4978695).sum := by decide
  have hdescent : baseEnd_4978695 < baseStart_4978695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4978695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4978721 : List Nat := [1, 2, 3, 2, 4, 1, 1, 1, 3, 2, 3]
def baseStart_4978721 : Nat := 118140960795 + 4978721 * 2 ^ 59
def prefixEnd_4978721 : Nat := 4983230072969 + 3 ^ 40 * 4978721 * 2
def baseEnd_4978721 : Nat := 2556476917633520464890785

theorem tailTrace_4978721 : CollatzResearch.WordTrace tailWord_4978721 prefixEnd_4978721 2556476917633520464890785 := by
  unfold tailWord_4978721
  simp only [CollatzResearch.WordTrace]
  refine ⟨181588872995951589696240017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121059248663967726464160011 181588872995951589696240017)
  ·
    refine ⟨136191654746963692272180013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181588872995951589696240017 136191654746963692272180013)
    ·
      refine ⟨51071870530111384602067505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136191654746963692272180013 51071870530111384602067505)
      ·
        refine ⟨38303902897583538451550629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51071870530111384602067505 38303902897583538451550629)
        ·
          refine ⟨7181981793296913459665743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38303902897583538451550629 7181981793296913459665743)
          ·
            refine ⟨10772972689945370189498615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7181981793296913459665743 10772972689945370189498615)
            ·
              refine ⟨16159459034918055284247923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10772972689945370189498615 16159459034918055284247923)
              ·
                refine ⟨24239188552377082926371885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16159459034918055284247923 24239188552377082926371885)
                ·
                  refine ⟨9089695707141406097389457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24239188552377082926371885 9089695707141406097389457)
                  ·
                    refine ⟨6817271780356054573042093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9089695707141406097389457 6817271780356054573042093)
                    ·
                      refine ⟨2556476917633520464890785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6817271780356054573042093 2556476917633520464890785)
                      ·
                        rfl

theorem cell23_4978721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_4978721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4978721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4978721 prefixEnd_4978721 := by exact prefixLift 4978721
  have htrace : WordTrace (prefixWord ++ tailWord_4978721) baseStart_4978721 baseEnd_4978721 := by
    simpa [prefixWord, tailWord_4978721, baseEnd_4978721] using wordTrace_append hprefix tailTrace_4978721
  have hstable : (prefixWord ++ tailWord_4978721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4978721).length < 2 ^ (prefixWord ++ tailWord_4978721).sum := by decide
  have hdescent : baseEnd_4978721 < baseStart_4978721 := by decide
  rcases family_descends (prefixWord ++ tailWord_4978721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4978738 : List Nat := [3, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3]
def baseStart_4978738 : Nat := 118140960795 + 4978738 * 2 ^ 59
def prefixEnd_4978738 : Nat := 4983230072969 + 3 ^ 40 * 4978738 * 2
def baseEnd_4978738 : Nat := 2556485646804646898378207

theorem tailTrace_4978738 : CollatzResearch.WordTrace tailWord_4978738 prefixEnd_4978738 2556485646804646898378207 := by
  unfold tailWord_4978738
  simp only [CollatzResearch.WordTrace]
  refine ⟨45397373259222500399902217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121059662024593334399739245 45397373259222500399902217)
  ·
    refine ⟨34048029944416875299926663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45397373259222500399902217 34048029944416875299926663)
    ·
      refine ⟨51072044916625312949889995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34048029944416875299926663 51072044916625312949889995)
      ·
        refine ⟨76608067374937969424834993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51072044916625312949889995 76608067374937969424834993)
        ·
          refine ⟨57456050531203477068626245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76608067374937969424834993 57456050531203477068626245)
          ·
            refine ⟨10773009474600651950367421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57456050531203477068626245 10773009474600651950367421)
            ·
              refine ⟨4039878552975244481387783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10773009474600651950367421 4039878552975244481387783)
              ·
                refine ⟨6059817829462866722081675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4039878552975244481387783 6059817829462866722081675)
                ·
                  refine ⟨9089726744194300083122513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6059817829462866722081675 9089726744194300083122513)
                  ·
                    refine ⟨6817295058145725062341885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9089726744194300083122513 6817295058145725062341885)
                    ·
                      refine ⟨2556485646804646898378207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6817295058145725062341885 2556485646804646898378207)
                      ·
                        rfl

theorem cell23_4978738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3].length) (baseStart_4978738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4978738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4978738 prefixEnd_4978738 := by exact prefixLift 4978738
  have htrace : WordTrace (prefixWord ++ tailWord_4978738) baseStart_4978738 baseEnd_4978738 := by
    simpa [prefixWord, tailWord_4978738, baseEnd_4978738] using wordTrace_append hprefix tailTrace_4978738
  have hstable : (prefixWord ++ tailWord_4978738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4978738).length < 2 ^ (prefixWord ++ tailWord_4978738).sum := by decide
  have hdescent : baseEnd_4978738 < baseStart_4978738 := by decide
  rcases family_descends (prefixWord ++ tailWord_4978738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4978751 : List Nat := [1, 1, 2, 2, 3, 1, 3, 4, 2, 1, 3]
def baseStart_4978751 : Nat := 118140960795 + 4978751 * 2 ^ 59
def prefixEnd_4978751 : Nat := 4983230072969 + 3 ^ 40 * 4978751 * 2
def baseEnd_4978751 : Nat := 2556492322053155347515647

theorem tailTrace_4978751 : CollatzResearch.WordTrace tailWord_4978751 prefixEnd_4978751 2556492322053155347515647 := by
  unfold tailWord_4978751
  simp only [CollatzResearch.WordTrace]
  refine ⟨181589967185842904819832107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121059978123895269879888071 181589967185842904819832107)
  ·
    refine ⟨272384950778764357229748161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181589967185842904819832107 272384950778764357229748161)
    ·
      refine ⟨204288713084073267922311121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 272384950778764357229748161 204288713084073267922311121)
      ·
        refine ⟨153216534813054950941733341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204288713084073267922311121 153216534813054950941733341)
        ·
          refine ⟨57456200554895606603150003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153216534813054950941733341 57456200554895606603150003)
          ·
            refine ⟨86184300832343409904725005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57456200554895606603150003 86184300832343409904725005)
            ·
              refine ⟨32319112812128778714271877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86184300832343409904725005 32319112812128778714271877)
              ·
                refine ⟨6059833652274146008925977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32319112812128778714271877 6059833652274146008925977)
                ·
                  refine ⟨4544875239205609506694483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6059833652274146008925977 4544875239205609506694483)
                  ·
                    refine ⟨6817312858808414260041725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4544875239205609506694483 6817312858808414260041725)
                    ·
                      refine ⟨2556492322053155347515647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6817312858808414260041725 2556492322053155347515647)
                      ·
                        rfl

theorem cell23_4978751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 4, 2, 1, 3].length) (baseStart_4978751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4978751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4978751 prefixEnd_4978751 := by exact prefixLift 4978751
  have htrace : WordTrace (prefixWord ++ tailWord_4978751) baseStart_4978751 baseEnd_4978751 := by
    simpa [prefixWord, tailWord_4978751, baseEnd_4978751] using wordTrace_append hprefix tailTrace_4978751
  have hstable : (prefixWord ++ tailWord_4978751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4978751).length < 2 ^ (prefixWord ++ tailWord_4978751).sum := by decide
  have hdescent : baseEnd_4978751 < baseStart_4978751 := by decide
  rcases family_descends (prefixWord ++ tailWord_4978751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4978752 : List Nat := [2, 1, 1, 2, 2, 6, 2, 2, 1, 2, 2]
def baseStart_4978752 : Nat := 118140960795 + 4978752 * 2 ^ 59
def prefixEnd_4978752 : Nat := 4983230072969 + 3 ^ 40 * 4978752 * 2
def baseEnd_4978752 : Nat := 2556492835533809843603143

theorem tailTrace_4978752 : CollatzResearch.WordTrace tailWord_4978752 prefixEnd_4978752 2556492835533809843603143 := by
  unfold tailWord_4978752
  simp only [CollatzResearch.WordTrace]
  refine ⟨90795001829419640995309255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121060002439226187993745673 90795001829419640995309255)
  ·
    refine ⟨136192502744129461492963883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90795001829419640995309255 136192502744129461492963883)
    ·
      refine ⟨204288754116194192239445825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136192502744129461492963883 204288754116194192239445825)
      ·
        refine ⟨153216565587145644179584369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204288754116194192239445825 153216565587145644179584369)
        ·
          refine ⟨114912424190359233134688277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153216565587145644179584369 114912424190359233134688277)
          ·
            refine ⟨5386519883923089053188513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 114912424190359233134688277 5386519883923089053188513)
            ·
              refine ⟨4039889912942316789891385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5386519883923089053188513 4039889912942316789891385)
              ·
                refine ⟨3029917434706737592418539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4039889912942316789891385 3029917434706737592418539)
                ·
                  refine ⟨4544876152060106388627809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3029917434706737592418539 4544876152060106388627809)
                  ·
                    refine ⟨3408657114045079791470857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4544876152060106388627809 3408657114045079791470857)
                    ·
                      refine ⟨2556492835533809843603143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3408657114045079791470857 2556492835533809843603143)
                      ·
                        rfl

theorem cell23_4978752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 2, 1, 2, 2].length) (baseStart_4978752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4978752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4978752 prefixEnd_4978752 := by exact prefixLift 4978752
  have htrace : WordTrace (prefixWord ++ tailWord_4978752) baseStart_4978752 baseEnd_4978752 := by
    simpa [prefixWord, tailWord_4978752, baseEnd_4978752] using wordTrace_append hprefix tailTrace_4978752
  have hstable : (prefixWord ++ tailWord_4978752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4978752).length < 2 ^ (prefixWord ++ tailWord_4978752).sum := by decide
  have hdescent : baseEnd_4978752 < baseStart_4978752 := by decide
  rcases family_descends (prefixWord ++ tailWord_4978752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4978767 : List Nat := [1, 1, 2, 1, 1, 2, 2, 5, 2, 6]
def baseStart_4978767 : Nat := 118140960795 + 4978767 * 2 ^ 59
def prefixEnd_4978767 : Nat := 4983230072969 + 3 ^ 40 * 4978767 * 2
def baseEnd_4978767 : Nat := 852166845914542428305191

theorem tailTrace_4978767 : CollatzResearch.WordTrace tailWord_4978767 prefixEnd_4978767 852166845914542428305191 := by
  unfold tailWord_4978767
  simp only [CollatzResearch.WordTrace]
  refine ⟨181590550753784939552414555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121060367169189959701609703 181590550753784939552414555)
  ·
    refine ⟨272385826130677409328621833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181590550753784939552414555 272385826130677409328621833)
    ·
      refine ⟨204289369598008056996466375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 272385826130677409328621833 204289369598008056996466375)
      ·
        refine ⟨306434054397012085494699563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204289369598008056996466375 306434054397012085494699563)
        ·
          refine ⟨459651081595518128242049345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 306434054397012085494699563 459651081595518128242049345)
          ·
            refine ⟨344738311196638596181537009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 459651081595518128242049345 344738311196638596181537009)
            ·
              refine ⟨258553733397478947136152757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 344738311196638596181537009 258553733397478947136152757)
              ·
                refine ⟨24239412506013651294014321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 258553733397478947136152757 24239412506013651294014321)
                ·
                  refine ⟨18179559379510238470510741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24239412506013651294014321 18179559379510238470510741)
                  ·
                    refine ⟨852166845914542428305191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18179559379510238470510741 852166845914542428305191)
                    ·
                      rfl

theorem cell23_4978767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2, 6].length) (baseStart_4978767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4978767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4978767 prefixEnd_4978767 := by exact prefixLift 4978767
  have htrace : WordTrace (prefixWord ++ tailWord_4978767) baseStart_4978767 baseEnd_4978767 := by
    simpa [prefixWord, tailWord_4978767, baseEnd_4978767] using wordTrace_append hprefix tailTrace_4978767
  have hstable : (prefixWord ++ tailWord_4978767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4978767).length < 2 ^ (prefixWord ++ tailWord_4978767).sum := by decide
  have hdescent : baseEnd_4978767 < baseStart_4978767 := by decide
  rcases family_descends (prefixWord ++ tailWord_4978767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4978791 : List Nat := [1, 1, 5, 1, 1, 2, 1, 4, 1, 4, 2]
def baseStart_4978791 : Nat := 118140960795 + 4978791 * 2 ^ 59
def prefixEnd_4978791 : Nat := 4983230072969 + 3 ^ 40 * 4978791 * 2
def baseEnd_4978791 : Nat := 2556512861279335191015463

theorem tailTrace_4978791 : CollatzResearch.WordTrace tailWord_4978791 prefixEnd_4978791 2556512861279335191015463 := by
  unfold tailWord_4978791
  simp only [CollatzResearch.WordTrace]
  refine ⟨181591426105697991651288227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121060950737131994434192151 181591426105697991651288227)
  ·
    refine ⟨272387139158546987476932341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181591426105697991651288227 272387139158546987476932341)
    ·
      refine ⟨25536294296113780075962407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 272387139158546987476932341 25536294296113780075962407)
      ·
        refine ⟨38304441444170670113943611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25536294296113780075962407 38304441444170670113943611)
        ·
          refine ⟨57456662166256005170915417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38304441444170670113943611 57456662166256005170915417)
          ·
            refine ⟨43092496624692003878186563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57456662166256005170915417 43092496624692003878186563)
            ·
              refine ⟨64638744937038005817279845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43092496624692003878186563 64638744937038005817279845)
              ·
                refine ⟨12119764675694626090739971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64638744937038005817279845 12119764675694626090739971)
                ·
                  refine ⟨18179647013541939136109957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12119764675694626090739971 18179647013541939136109957)
                  ·
                    refine ⟨3408683815039113588020617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18179647013541939136109957 3408683815039113588020617)
                    ·
                      refine ⟨2556512861279335191015463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3408683815039113588020617 2556512861279335191015463)
                      ·
                        rfl

theorem cell23_4978791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4, 1, 4, 2].length) (baseStart_4978791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4978791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4978791 prefixEnd_4978791 := by exact prefixLift 4978791
  have htrace : WordTrace (prefixWord ++ tailWord_4978791) baseStart_4978791 baseEnd_4978791 := by
    simpa [prefixWord, tailWord_4978791, baseEnd_4978791] using wordTrace_append hprefix tailTrace_4978791
  have hstable : (prefixWord ++ tailWord_4978791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4978791).length < 2 ^ (prefixWord ++ tailWord_4978791).sum := by decide
  have hdescent : baseEnd_4978791 < baseStart_4978791 := by decide
  rcases family_descends (prefixWord ++ tailWord_4978791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4978825 : List Nat := [1, 2, 1, 1, 4, 2, 5, 1, 2, 2, 2]
def baseStart_4978825 : Nat := 118140960795 + 4978825 * 2 ^ 59
def prefixEnd_4978825 : Nat := 4983230072969 + 3 ^ 40 * 4978825 * 2
def baseEnd_4978825 : Nat := 2556530319621588057990307

theorem tailTrace_4978825 : CollatzResearch.WordTrace tailWord_4978825 prefixEnd_4978825 2556530319621588057990307 := by
  unfold tailWord_4978825
  simp only [CollatzResearch.WordTrace]
  refine ⟨181592666187574815458025929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121061777458383210305350619 181592666187574815458025929)
  ·
    refine ⟨136194499640681111593519447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181592666187574815458025929 136194499640681111593519447)
    ·
      refine ⟨204291749461021667390279171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136194499640681111593519447 204291749461021667390279171)
      ·
        refine ⟨306437624191532501085418757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204291749461021667390279171 306437624191532501085418757)
        ·
          refine ⟨57457054535912343953516017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 306437624191532501085418757 57457054535912343953516017)
          ·
            refine ⟨43092790901934257965137013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57457054535912343953516017 43092790901934257965137013)
            ·
              refine ⟨4039949147056336684231595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43092790901934257965137013 4039949147056336684231595)
              ·
                refine ⟨6059923720584505026347393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4039949147056336684231595 6059923720584505026347393)
                ·
                  refine ⟨4544942790438378769760545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6059923720584505026347393 4544942790438378769760545)
                  ·
                    refine ⟨3408707092828784077320409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4544942790438378769760545 3408707092828784077320409)
                    ·
                      refine ⟨2556530319621588057990307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3408707092828784077320409 2556530319621588057990307)
                      ·
                        rfl

theorem cell23_4978825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 1, 2, 2, 2].length) (baseStart_4978825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4978825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4978825 prefixEnd_4978825 := by exact prefixLift 4978825
  have htrace : WordTrace (prefixWord ++ tailWord_4978825) baseStart_4978825 baseEnd_4978825 := by
    simpa [prefixWord, tailWord_4978825, baseEnd_4978825] using wordTrace_append hprefix tailTrace_4978825
  have hstable : (prefixWord ++ tailWord_4978825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4978825).length < 2 ^ (prefixWord ++ tailWord_4978825).sum := by decide
  have hdescent : baseEnd_4978825 < baseStart_4978825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4978825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4978844 : List Nat := [2, 2, 3, 2, 1, 1, 1, 3, 1, 7]
def baseStart_4978844 : Nat := 118140960795 + 4978844 * 2 ^ 59
def prefixEnd_4978844 : Nat := 4983230072969 + 3 ^ 40 * 4978844 * 2
def baseEnd_4978844 : Nat := 852180025251341161217573

theorem tailTrace_4978844 : CollatzResearch.WordTrace tailWord_4978844 prefixEnd_4978844 852180025251341161217573 := by
  unfold tailWord_4978844
  simp only [CollatzResearch.WordTrace]
  refine ⟨90796679587252990851483793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121062239449670654468645057 90796679587252990851483793)
  ·
    refine ⟨68097509690439743138612845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90796679587252990851483793 68097509690439743138612845)
    ·
      refine ⟨25536566133914903676979817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68097509690439743138612845 25536566133914903676979817)
      ·
        refine ⟨19152424600436177757734863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25536566133914903676979817 19152424600436177757734863)
        ·
          refine ⟨28728636900654266636602295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19152424600436177757734863 28728636900654266636602295)
          ·
            refine ⟨43092955350981399954903443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28728636900654266636602295 43092955350981399954903443)
            ·
              refine ⟨64639433026472099932355165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43092955350981399954903443 64639433026472099932355165)
              ·
                refine ⟨24239787384927037474633187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64639433026472099932355165 24239787384927037474633187)
                ·
                  refine ⟨36359681077390556211949781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24239787384927037474633187 36359681077390556211949781)
                  ·
                    refine ⟨852180025251341161217573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36359681077390556211949781 852180025251341161217573)
                    ·
                      rfl

theorem cell23_4978844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_4978844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4978844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4978844 prefixEnd_4978844 := by exact prefixLift 4978844
  have htrace : WordTrace (prefixWord ++ tailWord_4978844) baseStart_4978844 baseEnd_4978844 := by
    simpa [prefixWord, tailWord_4978844, baseEnd_4978844] using wordTrace_append hprefix tailTrace_4978844
  have hstable : (prefixWord ++ tailWord_4978844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4978844).length < 2 ^ (prefixWord ++ tailWord_4978844).sum := by decide
  have hdescent : baseEnd_4978844 < baseStart_4978844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4978844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4978848 : List Nat := [2, 1, 1, 4, 2, 4, 1, 3, 5]
def baseStart_4978848 : Nat := 118140960795 + 4978848 * 2 ^ 59
def prefixEnd_4978848 : Nat := 4983230072969 + 3 ^ 40 * 4978848 * 2
def baseEnd_4978848 : Nat := 284060236630737940889189

theorem tailTrace_4978848 : CollatzResearch.WordTrace tailWord_4978848 prefixEnd_4978848 284060236630737940889189 := by
  unfold tailWord_4978848
  simp only [CollatzResearch.WordTrace]
  refine ⟨90796752533245745193056599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121062336710994326924075465 90796752533245745193056599)
  ·
    refine ⟨136195128799868617789584899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90796752533245745193056599 136195128799868617789584899)
    ·
      refine ⟨204292693199802926684377349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136195128799868617789584899 204292693199802926684377349)
      ·
        refine ⟨38304879974963048753320753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 204292693199802926684377349 38304879974963048753320753)
        ·
          refine ⟨28728659981222286564990565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38304879974963048753320753 28728659981222286564990565)
          ·
            refine ⟨5386623746479178730935731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28728659981222286564990565 5386623746479178730935731)
            ·
              refine ⟨8079935619718768096403597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5386623746479178730935731 8079935619718768096403597)
              ·
                refine ⟨3029975857394538036151349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8079935619718768096403597 3029975857394538036151349)
                ·
                  refine ⟨284060236630737940889189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3029975857394538036151349 284060236630737940889189)
                  ·
                    rfl

theorem cell23_4978848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 3, 5].length) (baseStart_4978848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4978848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4978848 prefixEnd_4978848 := by exact prefixLift 4978848
  have htrace : WordTrace (prefixWord ++ tailWord_4978848) baseStart_4978848 baseEnd_4978848 := by
    simpa [prefixWord, tailWord_4978848, baseEnd_4978848] using wordTrace_append hprefix tailTrace_4978848
  have hstable : (prefixWord ++ tailWord_4978848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4978848).length < 2 ^ (prefixWord ++ tailWord_4978848).sum := by decide
  have hdescent : baseEnd_4978848 < baseStart_4978848 := by decide
  rcases family_descends (prefixWord ++ tailWord_4978848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4978861 : List Nat := [1, 5, 2, 1, 2, 1, 1, 1, 4, 5]
def baseStart_4978861 : Nat := 118140960795 + 4978861 * 2 ^ 59
def prefixEnd_4978861 : Nat := 4983230072969 + 3 ^ 40 * 4978861 * 2
def baseEnd_4978861 : Nat := 852182934975049972380047

theorem tailTrace_4978861 : CollatzResearch.WordTrace tailWord_4978861 prefixEnd_4978861 852182934975049972380047 := by
  unfold tailWord_4978861
  simp only [CollatzResearch.WordTrace]
  refine ⟨181593979215444393606336437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121062652810296262404224291 181593979215444393606336437)
  ·
    refine ⟨17024435551447911900594041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 181593979215444393606336437 17024435551447911900594041)
    ·
      refine ⟨12768326663585933925445531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17024435551447911900594041 12768326663585933925445531)
      ·
        refine ⟨19152489995378900888168297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12768326663585933925445531 19152489995378900888168297)
        ·
          refine ⟨14364367496534175666126223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19152489995378900888168297 14364367496534175666126223)
          ·
            refine ⟨21546551244801263499189335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14364367496534175666126223 21546551244801263499189335)
            ·
              refine ⟨32319826867201895248784003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21546551244801263499189335 32319826867201895248784003)
              ·
                refine ⟨48479740300802842873176005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32319826867201895248784003 48479740300802842873176005)
                ·
                  refine ⟨9089951306400533038720501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48479740300802842873176005 9089951306400533038720501)
                  ·
                    refine ⟨852182934975049972380047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9089951306400533038720501 852182934975049972380047)
                    ·
                      rfl

theorem cell23_4978861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_4978861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4978861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4978861 prefixEnd_4978861 := by exact prefixLift 4978861
  have htrace : WordTrace (prefixWord ++ tailWord_4978861) baseStart_4978861 baseEnd_4978861 := by
    simpa [prefixWord, tailWord_4978861, baseEnd_4978861] using wordTrace_append hprefix tailTrace_4978861
  have hstable : (prefixWord ++ tailWord_4978861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4978861).length < 2 ^ (prefixWord ++ tailWord_4978861).sum := by decide
  have hdescent : baseEnd_4978861 < baseStart_4978861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4978861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4978865 : List Nat := [1, 2, 2, 5, 2, 1, 3, 2, 5]
def baseStart_4978865 : Nat := 118140960795 + 4978865 * 2 ^ 59
def prefixEnd_4978865 : Nat := 4983230072969 + 3 ^ 40 * 4978865 * 2
def baseEnd_4978865 : Nat := 284061206538640877943347

theorem tailTrace_4978865 : CollatzResearch.WordTrace tailWord_4978865 prefixEnd_4978865 284061206538640877943347 := by
  unfold tailWord_4978865
  simp only [CollatzResearch.WordTrace]
  refine ⟨181594125107429902289482049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121062750071619934859654699 181594125107429902289482049)
  ·
    refine ⟨136195593830572426717111537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181594125107429902289482049 136195593830572426717111537)
    ·
      refine ⟨102146695372929320037833653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136195593830572426717111537 102146695372929320037833653)
      ·
        refine ⟨9576252691212123753546905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 102146695372929320037833653 9576252691212123753546905)
        ·
          refine ⟨7182189518409092815160179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9576252691212123753546905 7182189518409092815160179)
          ·
            refine ⟨10773284277613639222740269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7182189518409092815160179 10773284277613639222740269)
            ·
              refine ⟨4039981604105114708527601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10773284277613639222740269 4039981604105114708527601)
              ·
                refine ⟨3029986203078836031395701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4039981604105114708527601 3029986203078836031395701)
                ·
                  refine ⟨284061206538640877943347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3029986203078836031395701 284061206538640877943347)
                  ·
                    rfl

theorem cell23_4978865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 2, 5].length) (baseStart_4978865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4978865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4978865 prefixEnd_4978865 := by exact prefixLift 4978865
  have htrace : WordTrace (prefixWord ++ tailWord_4978865) baseStart_4978865 baseEnd_4978865 := by
    simpa [prefixWord, tailWord_4978865, baseEnd_4978865] using wordTrace_append hprefix tailTrace_4978865
  have hstable : (prefixWord ++ tailWord_4978865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4978865).length < 2 ^ (prefixWord ++ tailWord_4978865).sum := by decide
  have hdescent : baseEnd_4978865 < baseStart_4978865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4978865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4978898 : List Nat := [3, 2, 2, 2, 1, 3, 2, 1, 2, 1, 4]
def baseStart_4978898 : Nat := 118140960795 + 4978898 * 2 ^ 59
def prefixEnd_4978898 : Nat := 4983230072969 + 3 ^ 40 * 4978898 * 2
def baseEnd_4978898 : Nat := 2556567803709366272377471

theorem tailTrace_4978898 : CollatzResearch.WordTrace tailWord_4978898 prefixEnd_4978898 2556567803709366272377471 := by
  unfold tailWord_4978898
  simp only [CollatzResearch.WordTrace]
  refine ⟨45398832179077587231358337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121063552477540232616955565 45398832179077587231358337)
  ·
    refine ⟨34049124134308190423518753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45398832179077587231358337 34049124134308190423518753)
    ·
      refine ⟨25536843100731142817639065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34049124134308190423518753 25536843100731142817639065)
      ·
        refine ⟨19152632325548357113229299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25536843100731142817639065 19152632325548357113229299)
        ·
          refine ⟨28728948488322535669843949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19152632325548357113229299 28728948488322535669843949)
          ·
            refine ⟨10773355683120950876191481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28728948488322535669843949 10773355683120950876191481)
            ·
              refine ⟨8080016762340713157143611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10773355683120950876191481 8080016762340713157143611)
              ·
                refine ⟨12120025143511069735715417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8080016762340713157143611 12120025143511069735715417)
                ·
                  refine ⟨9090018857633302301786563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12120025143511069735715417 9090018857633302301786563)
                  ·
                    refine ⟨13635028286449953452679845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9090018857633302301786563 13635028286449953452679845)
                    ·
                      refine ⟨2556567803709366272377471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13635028286449953452679845 2556567803709366272377471)
                      ·
                        rfl

theorem cell23_4978898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_4978898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4978898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4978898 prefixEnd_4978898 := by exact prefixLift 4978898
  have htrace : WordTrace (prefixWord ++ tailWord_4978898) baseStart_4978898 baseEnd_4978898 := by
    simpa [prefixWord, tailWord_4978898, baseEnd_4978898] using wordTrace_append hprefix tailTrace_4978898
  have hstable : (prefixWord ++ tailWord_4978898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4978898).length < 2 ^ (prefixWord ++ tailWord_4978898).sum := by decide
  have hdescent : baseEnd_4978898 < baseStart_4978898 := by decide
  rcases family_descends (prefixWord ++ tailWord_4978898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4978924 : List Nat := [2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 6]
def baseStart_4978924 : Nat := 118140960795 + 4978924 * 2 ^ 59
def prefixEnd_4978924 : Nat := 4983230072969 + 3 ^ 40 * 4978924 * 2
def baseEnd_4978924 : Nat := 2556581154206383170652351

theorem tailTrace_4978924 : CollatzResearch.WordTrace tailWord_4978924 prefixEnd_4978924 2556581154206383170652351 := by
  unfold tailWord_4978924
  simp only [CollatzResearch.WordTrace]
  refine ⟨90798138507108077682939913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121064184676144103577253217 90798138507108077682939913)
  ·
    refine ⟨68098603880331058262204935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90798138507108077682939913 68098603880331058262204935)
    ·
      refine ⟨102147905820496587393307403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68098603880331058262204935 102147905820496587393307403)
      ·
        refine ⟨153221858730744881089961105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102147905820496587393307403 153221858730744881089961105)
        ·
          refine ⟨114916394048058660817470829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153221858730744881089961105 114916394048058660817470829)
          ·
            refine ⟨43093647768021997806551561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114916394048058660817470829 43093647768021997806551561)
            ·
              refine ⟨32320235826016498354913671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43093647768021997806551561 32320235826016498354913671)
              ·
                refine ⟨48480353739024747532370507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32320235826016498354913671 48480353739024747532370507)
                ·
                  refine ⟨72720530608537121298555761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48480353739024747532370507 72720530608537121298555761)
                  ·
                    refine ⟨54540397956402840973916821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 72720530608537121298555761 54540397956402840973916821)
                    ·
                      refine ⟨2556581154206383170652351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54540397956402840973916821 2556581154206383170652351)
                      ·
                        rfl

theorem cell23_4978924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 6].length) (baseStart_4978924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4978924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4978924 prefixEnd_4978924 := by exact prefixLift 4978924
  have htrace : WordTrace (prefixWord ++ tailWord_4978924) baseStart_4978924 baseEnd_4978924 := by
    simpa [prefixWord, tailWord_4978924, baseEnd_4978924] using wordTrace_append hprefix tailTrace_4978924
  have hstable : (prefixWord ++ tailWord_4978924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4978924).length < 2 ^ (prefixWord ++ tailWord_4978924).sum := by decide
  have hdescent : baseEnd_4978924 < baseStart_4978924 := by decide
  rcases family_descends (prefixWord ++ tailWord_4978924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4978958 : List Nat := [4, 1, 1, 2, 1, 2, 3, 1, 1, 5, 2]
def baseStart_4978958 : Nat := 118140960795 + 4978958 * 2 ^ 59
def prefixEnd_4978958 : Nat := 4983230072969 + 3 ^ 40 * 4978958 * 2
def baseEnd_4978958 : Nat := 2556598612548636037627195

theorem tailTrace_4978958 : CollatzResearch.WordTrace tailWord_4978958 prefixEnd_4978958 2556598612548636037627195 := by
  unfold tailWord_4978958
  simp only [CollatzResearch.WordTrace]
  refine ⟨22699689637011622396577191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121065011397395319448411685 22699689637011622396577191)
  ·
    refine ⟨34049534455517433594865787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22699689637011622396577191 34049534455517433594865787)
    ·
      refine ⟨51074301683276150392298681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34049534455517433594865787 51074301683276150392298681)
      ·
        refine ⟨38305726262457112794224011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51074301683276150392298681 38305726262457112794224011)
        ·
          refine ⟨57458589393685669191336017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38305726262457112794224011 57458589393685669191336017)
          ·
            refine ⟨43093942045264251893502013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57458589393685669191336017 43093942045264251893502013)
            ·
              refine ⟨16160228266974094460063255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43093942045264251893502013 16160228266974094460063255)
              ·
                refine ⟨24240342400461141690094883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16160228266974094460063255 24240342400461141690094883)
                ·
                  refine ⟨36360513600691712535142325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24240342400461141690094883 36360513600691712535142325)
                  ·
                    refine ⟨3408798150064848050169593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36360513600691712535142325 3408798150064848050169593)
                    ·
                      refine ⟨2556598612548636037627195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3408798150064848050169593 2556598612548636037627195)
                      ·
                        rfl

theorem cell23_4978958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 1, 5, 2].length) (baseStart_4978958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4978958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4978958 prefixEnd_4978958 := by exact prefixLift 4978958
  have htrace : WordTrace (prefixWord ++ tailWord_4978958) baseStart_4978958 baseEnd_4978958 := by
    simpa [prefixWord, tailWord_4978958, baseEnd_4978958] using wordTrace_append hprefix tailTrace_4978958
  have hstable : (prefixWord ++ tailWord_4978958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4978958).length < 2 ^ (prefixWord ++ tailWord_4978958).sum := by decide
  have hdescent : baseEnd_4978958 < baseStart_4978958 := by decide
  rcases family_descends (prefixWord ++ tailWord_4978958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4978965 : List Nat := [1, 3, 2, 1, 2, 1, 3, 5, 1, 1, 3]
def baseStart_4978965 : Nat := 118140960795 + 4978965 * 2 ^ 59
def prefixEnd_4978965 : Nat := 4983230072969 + 3 ^ 40 * 4978965 * 2
def baseEnd_4978965 : Nat := 2556602206913217510239663

theorem tailTrace_4978965 : CollatzResearch.WordTrace tailWord_4978965 prefixEnd_4978965 2556602206913217510239663 := by
  unfold tailWord_4978965
  simp only [CollatzResearch.WordTrace]
  refine ⟨181597772407067619368122349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121065181604711746245414899 181597772407067619368122349)
  ·
    refine ⟨68099164652650357263045881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181597772407067619368122349 68099164652650357263045881)
    ·
      refine ⟨51074373489487767947284411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68099164652650357263045881 51074373489487767947284411)
      ·
        refine ⟨76611560234231651920926617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51074373489487767947284411 76611560234231651920926617)
        ·
          refine ⟨57458670175673738940694963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76611560234231651920926617 57458670175673738940694963)
          ·
            refine ⟨86188005263510608411042445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57458670175673738940694963 86188005263510608411042445)
            ·
              refine ⟨32320501973816478154140917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86188005263510608411042445 32320501973816478154140917)
              ·
                refine ⟨3030047060045294826950711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32320501973816478154140917 3030047060045294826950711)
                ·
                  refine ⟨4545070590067942240426067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3030047060045294826950711 4545070590067942240426067)
                  ·
                    refine ⟨6817605885101913360639101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4545070590067942240426067 6817605885101913360639101)
                    ·
                      refine ⟨2556602206913217510239663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6817605885101913360639101 2556602206913217510239663)
                      ·
                        rfl

theorem cell23_4978965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 5, 1, 1, 3].length) (baseStart_4978965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4978965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4978965 prefixEnd_4978965 := by exact prefixLift 4978965
  have htrace : WordTrace (prefixWord ++ tailWord_4978965) baseStart_4978965 baseEnd_4978965 := by
    simpa [prefixWord, tailWord_4978965, baseEnd_4978965] using wordTrace_append hprefix tailTrace_4978965
  have hstable : (prefixWord ++ tailWord_4978965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4978965).length < 2 ^ (prefixWord ++ tailWord_4978965).sum := by decide
  have hdescent : baseEnd_4978965 < baseStart_4978965 := by decide
  rcases family_descends (prefixWord ++ tailWord_4978965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4978991 : List Nat := [1, 1, 2, 1, 2, 1, 4, 1, 5, 2, 3]
def baseStart_4978991 : Nat := 118140960795 + 4978991 * 2 ^ 59
def prefixEnd_4978991 : Nat := 4983230072969 + 3 ^ 40 * 4978991 * 2
def baseEnd_4978991 : Nat := 2556615557410234408514543

theorem tailTrace_4978991 : CollatzResearch.WordTrace tailWord_4978991 prefixEnd_4978991 2556615557410234408514543 := by
  unfold tailWord_4978991
  simp only [CollatzResearch.WordTrace]
  refine ⟨181598720704973425808568827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121065813803315617205712551 181598720704973425808568827)
  ·
    refine ⟨272398081057460138712853241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181598720704973425808568827 272398081057460138712853241)
    ·
      refine ⟨204298560793095104034639931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 272398081057460138712853241 204298560793095104034639931)
      ·
        refine ⟨306447841189642656051959897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204298560793095104034639931 306447841189642656051959897)
        ·
          refine ⟨229835880892231992038969923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 306447841189642656051959897 229835880892231992038969923)
          ·
            refine ⟨344753821338347988058454885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229835880892231992038969923 344753821338347988058454885)
            ·
              refine ⟨64641341500940247760960291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 344753821338347988058454885 64641341500940247760960291)
              ·
                refine ⟨96962012251410371641440437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64641341500940247760960291 96962012251410371641440437)
                ·
                  refine ⟨9090188648569722341385041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 96962012251410371641440437 9090188648569722341385041)
                  ·
                    refine ⟨6817641486427291756038781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9090188648569722341385041 6817641486427291756038781)
                    ·
                      refine ⟨2556615557410234408514543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6817641486427291756038781 2556615557410234408514543)
                      ·
                        rfl

theorem cell23_4978991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 5, 2, 3].length) (baseStart_4978991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4978991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4978991 prefixEnd_4978991 := by exact prefixLift 4978991
  have htrace : WordTrace (prefixWord ++ tailWord_4978991) baseStart_4978991 baseEnd_4978991 := by
    simpa [prefixWord, tailWord_4978991, baseEnd_4978991] using wordTrace_append hprefix tailTrace_4978991
  have hstable : (prefixWord ++ tailWord_4978991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4978991).length < 2 ^ (prefixWord ++ tailWord_4978991).sum := by decide
  have hdescent : baseEnd_4978991 < baseStart_4978991 := by decide
  rcases family_descends (prefixWord ++ tailWord_4978991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4979011 : List Nat := [1, 1, 1, 3, 1, 3, 6, 7]
def baseStart_4979011 : Nat := 118140960795 + 4979011 * 2 ^ 59
def prefixEnd_4979011 : Nat := 4983230072969 + 3 ^ 40 * 4979011 * 2
def baseEnd_4979011 : Nat := 94689845445308308528313

theorem tailTrace_4979011 : CollatzResearch.WordTrace tailWord_4979011 prefixEnd_4979011 94689845445308308528313 := by
  unfold tailWord_4979011
  simp only [CollatzResearch.WordTrace]
  refine ⟨181599450164900969224296887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121066300109933979482864591 181599450164900969224296887)
  ·
    refine ⟨272399175247351453836445331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181599450164900969224296887 272399175247351453836445331)
    ·
      refine ⟨408598762871027180754667997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272399175247351453836445331 408598762871027180754667997)
      ·
        refine ⟨153224536076635192783000499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 408598762871027180754667997 153224536076635192783000499)
        ·
          refine ⟨229836804114952789174500749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153224536076635192783000499 229836804114952789174500749)
          ·
            refine ⟨86188801543107295940437781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 229836804114952789174500749 86188801543107295940437781)
            ·
              refine ⟨4040100072333154497208021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 86188801543107295940437781 4040100072333154497208021)
              ·
                refine ⟨94689845445308308528313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4040100072333154497208021 94689845445308308528313)
                ·
                  rfl

theorem cell23_4979011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 7].length) (baseStart_4979011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4979011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4979011 prefixEnd_4979011 := by exact prefixLift 4979011
  have htrace : WordTrace (prefixWord ++ tailWord_4979011) baseStart_4979011 baseEnd_4979011 := by
    simpa [prefixWord, tailWord_4979011, baseEnd_4979011] using wordTrace_append hprefix tailTrace_4979011
  have hstable : (prefixWord ++ tailWord_4979011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4979011).length < 2 ^ (prefixWord ++ tailWord_4979011).sum := by decide
  have hdescent : baseEnd_4979011 < baseStart_4979011 := by decide
  rcases family_descends (prefixWord ++ tailWord_4979011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4979022 : List Nat := [4, 1, 1, 1, 1, 1, 2, 7, 1, 2, 2]
def baseStart_4979022 : Nat := 118140960795 + 4979022 * 2 ^ 59
def prefixEnd_4979022 : Nat := 4983230072969 + 3 ^ 40 * 4979022 * 2
def baseEnd_4979022 : Nat := 2556631475310523787226901

theorem tailTrace_4979022 : CollatzResearch.WordTrace tailWord_4979022 prefixEnd_4979022 2556631475310523787226901 := by
  unfold tailWord_4979022
  simp only [CollatzResearch.WordTrace]
  refine ⟨22699981420982639762868415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121066567578574078735298213 22699981420982639762868415)
  ·
    refine ⟨34049972131473959644302623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22699981420982639762868415 34049972131473959644302623)
    ·
      refine ⟨51074958197210939466453935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34049972131473959644302623 51074958197210939466453935)
      ·
        refine ⟨76612437295816409199680903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51074958197210939466453935 76612437295816409199680903)
        ·
          refine ⟨114918655943724613799521355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76612437295816409199680903 114918655943724613799521355)
          ·
            refine ⟨172377983915586920699282033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114918655943724613799521355 172377983915586920699282033)
            ·
              refine ⟨129283487936690190524461525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 172377983915586920699282033 129283487936690190524461525)
              ·
                refine ⟨3030081748516176340417067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 129283487936690190524461525 3030081748516176340417067)
                ·
                  refine ⟨4545122622774264510625601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3030081748516176340417067 4545122622774264510625601)
                  ·
                    refine ⟨3408841967080698382969201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4545122622774264510625601 3408841967080698382969201)
                    ·
                      refine ⟨2556631475310523787226901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3408841967080698382969201 2556631475310523787226901)
                      ·
                        rfl

theorem cell23_4979022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 7, 1, 2, 2].length) (baseStart_4979022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4979022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4979022 prefixEnd_4979022 := by exact prefixLift 4979022
  have htrace : WordTrace (prefixWord ++ tailWord_4979022) baseStart_4979022 baseEnd_4979022 := by
    simpa [prefixWord, tailWord_4979022, baseEnd_4979022] using wordTrace_append hprefix tailTrace_4979022
  have hstable : (prefixWord ++ tailWord_4979022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4979022).length < 2 ^ (prefixWord ++ tailWord_4979022).sum := by decide
  have hdescent : baseEnd_4979022 < baseStart_4979022 := by decide
  rcases family_descends (prefixWord ++ tailWord_4979022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4979095 : List Nat := [1, 1, 3, 3, 1, 1, 2, 3, 4, 2, 2]
def baseStart_4979095 : Nat := 118140960795 + 4979095 * 2 ^ 59
def prefixEnd_4979095 : Nat := 4983230072969 + 3 ^ 40 * 4979095 * 2
def baseEnd_4979095 : Nat := 2556668959398302001614065

theorem tailTrace_4979095 : CollatzResearch.WordTrace tailWord_4979095 prefixEnd_4979095 2556668959398302001614065 := by
  unfold tailWord_4979095
  simp only [CollatzResearch.WordTrace]
  refine ⟨181602513896596651570354739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121068342597731101046903159 181602513896596651570354739)
  ·
    refine ⟨272403770844894977355532109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181602513896596651570354739 272403770844894977355532109)
    ·
      refine ⟨102151414066835616508324541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 272403770844894977355532109 102151414066835616508324541)
      ·
        refine ⟨38306780275063356190621703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102151414066835616508324541 38306780275063356190621703)
        ·
          refine ⟨57460170412595034285932555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38306780275063356190621703 57460170412595034285932555)
          ·
            refine ⟨86190255618892551428898833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57460170412595034285932555 86190255618892551428898833)
            ·
              refine ⟨64642691714169413571674125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86190255618892551428898833 64642691714169413571674125)
              ·
                refine ⟨24241009392813530089377797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64642691714169413571674125 24241009392813530089377797)
                ·
                  refine ⟨4545189261152536891758337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24241009392813530089377797 4545189261152536891758337)
                  ·
                    refine ⟨3408891945864402668818753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4545189261152536891758337 3408891945864402668818753)
                    ·
                      refine ⟨2556668959398302001614065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3408891945864402668818753 2556668959398302001614065)
                      ·
                        rfl

theorem cell23_4979095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 4, 2, 2].length) (baseStart_4979095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4979095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4979095 prefixEnd_4979095 := by exact prefixLift 4979095
  have htrace : WordTrace (prefixWord ++ tailWord_4979095) baseStart_4979095 baseEnd_4979095 := by
    simpa [prefixWord, tailWord_4979095, baseEnd_4979095] using wordTrace_append hprefix tailTrace_4979095
  have hstable : (prefixWord ++ tailWord_4979095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4979095).length < 2 ^ (prefixWord ++ tailWord_4979095).sum := by decide
  have hdescent : baseEnd_4979095 < baseStart_4979095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4979095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4979098 : List Nat := [3, 1, 1, 4, 1, 2, 1, 1, 2, 4, 3]
def baseStart_4979098 : Nat := 118140960795 + 4979098 * 2 ^ 59
def prefixEnd_4979098 : Nat := 4983230072969 + 3 ^ 40 * 4979098 * 2
def baseEnd_4979098 : Nat := 2556670499840265489876551

theorem tailTrace_4979098 : CollatzResearch.WordTrace tailWord_4979098 prefixEnd_4979098 2556670499840265489876551 := by
  unfold tailWord_4979098
  simp only [CollatzResearch.WordTrace]
  refine ⟨45400655828896445770678487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121068415543723855388475965 45400655828896445770678487)
  ·
    refine ⟨68100983743344668656017731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45400655828896445770678487 68100983743344668656017731)
    ·
      refine ⟨102151475615017002984026597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68100983743344668656017731 102151475615017002984026597)
      ·
        refine ⟨19153401677815688059504987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102151475615017002984026597 19153401677815688059504987)
        ·
          refine ⟨28730102516723532089257481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19153401677815688059504987 28730102516723532089257481)
          ·
            refine ⟨21547576887542649066943111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28730102516723532089257481 21547576887542649066943111)
            ·
              refine ⟨32321365331313973600414667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21547576887542649066943111 32321365331313973600414667)
              ·
                refine ⟨48482047996970960400622001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32321365331313973600414667 48482047996970960400622001)
                ·
                  refine ⟨36361535997728220300466501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48482047996970960400622001 36361535997728220300466501)
                  ·
                    refine ⟨6817787999574041306337469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36361535997728220300466501 6817787999574041306337469)
                    ·
                      refine ⟨2556670499840265489876551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6817787999574041306337469 2556670499840265489876551)
                      ·
                        rfl

theorem cell23_4979098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_4979098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4979098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4979098 prefixEnd_4979098 := by exact prefixLift 4979098
  have htrace : WordTrace (prefixWord ++ tailWord_4979098) baseStart_4979098 baseEnd_4979098 := by
    simpa [prefixWord, tailWord_4979098, baseEnd_4979098] using wordTrace_append hprefix tailTrace_4979098
  have hstable : (prefixWord ++ tailWord_4979098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4979098).length < 2 ^ (prefixWord ++ tailWord_4979098).sum := by decide
  have hdescent : baseEnd_4979098 < baseStart_4979098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4979098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4979105 : List Nat := [1, 2, 3, 5, 1, 1, 1, 1, 2, 6]
def baseStart_4979105 : Nat := 118140960795 + 4979105 * 2 ^ 59
def prefixEnd_4979105 : Nat := 4983230072969 + 3 ^ 40 * 4979105 * 2
def baseEnd_4979105 : Nat := 852224698068282320829673

theorem tailTrace_4979105 : CollatzResearch.WordTrace tailWord_4979105 prefixEnd_4979105 852224698068282320829673 := by
  unfold tailWord_4979105
  simp only [CollatzResearch.WordTrace]
  refine ⟨181602878626560423278218769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121068585751040282185479179 181602878626560423278218769)
  ·
    refine ⟨136202158969920317458664077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181602878626560423278218769 136202158969920317458664077)
    ·
      refine ⟨51075809613720119046999029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136202158969920317458664077 51075809613720119046999029)
      ·
        refine ⟨4788357151286261160656159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51075809613720119046999029 4788357151286261160656159)
        ·
          refine ⟨7182535726929391740984239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4788357151286261160656159 7182535726929391740984239)
          ·
            refine ⟨10773803590394087611476359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7182535726929391740984239 10773803590394087611476359)
            ·
              refine ⟨16160705385591131417214539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10773803590394087611476359 16160705385591131417214539)
              ·
                refine ⟨24241058078386697125821809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16160705385591131417214539 24241058078386697125821809)
                ·
                  refine ⟨18180793558790022844366357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24241058078386697125821809 18180793558790022844366357)
                  ·
                    refine ⟨852224698068282320829673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18180793558790022844366357 852224698068282320829673)
                    ·
                      rfl

theorem cell23_4979105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 2, 6].length) (baseStart_4979105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4979105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4979105 prefixEnd_4979105 := by exact prefixLift 4979105
  have htrace : WordTrace (prefixWord ++ tailWord_4979105) baseStart_4979105 baseEnd_4979105 := by
    simpa [prefixWord, tailWord_4979105, baseEnd_4979105] using wordTrace_append hprefix tailTrace_4979105
  have hstable : (prefixWord ++ tailWord_4979105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4979105).length < 2 ^ (prefixWord ++ tailWord_4979105).sum := by decide
  have hdescent : baseEnd_4979105 < baseStart_4979105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4979105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4979112 : List Nat := [2, 1, 6, 1, 1, 1, 1, 3, 1, 4, 2]
def baseStart_4979112 : Nat := 118140960795 + 4979112 * 2 ^ 59
def prefixEnd_4979112 : Nat := 4983230072969 + 3 ^ 40 * 4979112 * 2
def baseEnd_4979112 : Nat := 2556677688569428435101487

theorem tailTrace_4979112 : CollatzResearch.WordTrace tailWord_4979112 prefixEnd_4979112 2556677688569428435101487 := by
  unfold tailWord_4979112
  simp only [CollatzResearch.WordTrace]
  refine ⟨90801566968767531736861795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121068755958356708982482393 90801566968767531736861795)
  ·
    refine ⟨136202350453151297605292693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90801566968767531736861795 136202350453151297605292693)
    ·
      refine ⟨6384485177491467075248095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 136202350453151297605292693 6384485177491467075248095)
      ·
        refine ⟨9576727766237200612872143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6384485177491467075248095 9576727766237200612872143)
        ·
          refine ⟨14365091649355800919308215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9576727766237200612872143 14365091649355800919308215)
          ·
            refine ⟨21547637474033701378962323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14365091649355800919308215 21547637474033701378962323)
            ·
              refine ⟨32321456211050552068443485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21547637474033701378962323 32321456211050552068443485)
              ·
                refine ⟨12120546079143957025666307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32321456211050552068443485 12120546079143957025666307)
                ·
                  refine ⟨18180819118715935538499461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12120546079143957025666307 18180819118715935538499461)
                  ·
                    refine ⟨3408903584759237913468649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18180819118715935538499461 3408903584759237913468649)
                    ·
                      refine ⟨2556677688569428435101487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3408903584759237913468649 2556677688569428435101487)
                      ·
                        rfl

theorem cell23_4979112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_4979112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4979112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4979112 prefixEnd_4979112 := by exact prefixLift 4979112
  have htrace : WordTrace (prefixWord ++ tailWord_4979112) baseStart_4979112 baseEnd_4979112 := by
    simpa [prefixWord, tailWord_4979112, baseEnd_4979112] using wordTrace_append hprefix tailTrace_4979112
  have hstable : (prefixWord ++ tailWord_4979112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4979112).length < 2 ^ (prefixWord ++ tailWord_4979112).sum := by decide
  have hdescent : baseEnd_4979112 < baseStart_4979112 := by decide
  rcases family_descends (prefixWord ++ tailWord_4979112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4979131 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 8, 5]
def baseStart_4979131 : Nat := 118140960795 + 4979131 * 2 ^ 59
def prefixEnd_4979131 : Nat := 4983230072969 + 3 ^ 40 * 4979131 * 2
def baseEnd_4979131 : Nat := 852229148233954620254633

theorem tailTrace_4979131 : CollatzResearch.WordTrace tailWord_4979131 prefixEnd_4979131 852229148233954620254633 := by
  unfold tailWord_4979131
  simp only [CollatzResearch.WordTrace]
  refine ⟨181603826924466229718665247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121069217949644153145776831 181603826924466229718665247)
  ·
    refine ⟨272405740386699344577997871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181603826924466229718665247 272405740386699344577997871)
    ·
      refine ⟨408608610580049016866996807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272405740386699344577997871 408608610580049016866996807)
      ·
        refine ⟨612912915870073525300495211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 408608610580049016866996807 612912915870073525300495211)
        ·
          refine ⟨919369373805110287950742817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 612912915870073525300495211 919369373805110287950742817)
          ·
            refine ⟨689527030353832715963057113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 919369373805110287950742817 689527030353832715963057113)
            ·
              refine ⟨517145272765374536972292835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 689527030353832715963057113 517145272765374536972292835)
              ·
                refine ⟨775717909148061805458439253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 517145272765374536972292835 775717909148061805458439253)
                ·
                  refine ⟨9090444247828849282716085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 775717909148061805458439253 9090444247828849282716085)
                  ·
                    refine ⟨852229148233954620254633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9090444247828849282716085 852229148233954620254633)
                    ·
                      rfl

theorem cell23_4979131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 8, 5].length) (baseStart_4979131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4979131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4979131 prefixEnd_4979131 := by exact prefixLift 4979131
  have htrace : WordTrace (prefixWord ++ tailWord_4979131) baseStart_4979131 baseEnd_4979131 := by
    simpa [prefixWord, tailWord_4979131, baseEnd_4979131] using wordTrace_append hprefix tailTrace_4979131
  have hstable : (prefixWord ++ tailWord_4979131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4979131).length < 2 ^ (prefixWord ++ tailWord_4979131).sum := by decide
  have hdescent : baseEnd_4979131 < baseStart_4979131 := by decide
  rcases family_descends (prefixWord ++ tailWord_4979131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4979208 : List Nat := [2, 1, 3, 2, 1, 1, 1, 6, 6]
def baseStart_4979208 : Nat := 118140960795 + 4979208 * 2 ^ 59
def prefixEnd_4979208 : Nat := 4983230072969 + 3 ^ 40 * 4979208 * 2
def baseEnd_4979208 : Nat := 284080775856917784389005

theorem tailTrace_4979208 : CollatzResearch.WordTrace tailWord_4979208 prefixEnd_4979208 284080775856917784389005 := by
  unfold tailWord_4979208
  simp only [CollatzResearch.WordTrace]
  refine ⟨90803317672593635934609139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121071090230124847912812185 90803317672593635934609139)
  ·
    refine ⟨136204976508890453901913709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90803317672593635934609139 136204976508890453901913709)
    ·
      refine ⟨51076866190833920213217641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136204976508890453901913709 51076866190833920213217641)
      ·
        refine ⟨38307649643125440159913231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51076866190833920213217641 38307649643125440159913231)
        ·
          refine ⟨57461474464688160239869847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38307649643125440159913231 57461474464688160239869847)
          ·
            refine ⟨86192211697032240359804771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57461474464688160239869847 86192211697032240359804771)
            ·
              refine ⟨129288317545548360539707157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86192211697032240359804771 129288317545548360539707157)
              ·
                refine ⟨6060389884947579400298773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 129288317545548360539707157 6060389884947579400298773)
                ·
                  refine ⟨284080775856917784389005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6060389884947579400298773 284080775856917784389005)
                  ·
                    rfl

theorem cell23_4979208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 6, 6].length) (baseStart_4979208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4979208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4979208 prefixEnd_4979208 := by exact prefixLift 4979208
  have htrace : WordTrace (prefixWord ++ tailWord_4979208) baseStart_4979208 baseEnd_4979208 := by
    simpa [prefixWord, tailWord_4979208, baseEnd_4979208] using wordTrace_append hprefix tailTrace_4979208
  have hstable : (prefixWord ++ tailWord_4979208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4979208).length < 2 ^ (prefixWord ++ tailWord_4979208).sum := by decide
  have hdescent : baseEnd_4979208 < baseStart_4979208 := by decide
  rcases family_descends (prefixWord ++ tailWord_4979208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4979212 : List Nat := [2, 2, 1, 2, 4, 3, 1, 1, 3, 4]
def baseStart_4979212 : Nat := 118140960795 + 4979212 * 2 ^ 59
def prefixEnd_4979212 : Nat := 4983230072969 + 3 ^ 40 * 4979212 * 2
def baseEnd_4979212 : Nat := 852243012211626014617009

theorem tailTrace_4979212 : CollatzResearch.WordTrace tailWord_4979212 prefixEnd_4979212 852243012211626014617009 := by
  unfold tailWord_4979212
  simp only [CollatzResearch.WordTrace]
  refine ⟨90803390618586390276181945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121071187491448520368242593 90803390618586390276181945)
  ·
    refine ⟨68102542963939792707136459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90803390618586390276181945 68102542963939792707136459)
    ·
      refine ⟨102153814445909689060704689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68102542963939792707136459 102153814445909689060704689)
      ·
        refine ⟨76615360834432266795528517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102153814445909689060704689 76615360834432266795528517)
        ·
          refine ⟨14365380156456050024161597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76615360834432266795528517 14365380156456050024161597)
          ·
            refine ⟨5387017558671018759060599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14365380156456050024161597 5387017558671018759060599)
            ·
              refine ⟨8080526338006528138590899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5387017558671018759060599 8080526338006528138590899)
              ·
                refine ⟨12120789507009792207886349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8080526338006528138590899 12120789507009792207886349)
                ·
                  refine ⟨4545296065128672077957381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12120789507009792207886349 4545296065128672077957381)
                  ·
                    refine ⟨852243012211626014617009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4545296065128672077957381 852243012211626014617009)
                    ·
                      rfl

theorem cell23_4979212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 1, 3, 4].length) (baseStart_4979212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4979212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4979212 prefixEnd_4979212 := by exact prefixLift 4979212
  have htrace : WordTrace (prefixWord ++ tailWord_4979212) baseStart_4979212 baseEnd_4979212 := by
    simpa [prefixWord, tailWord_4979212, baseEnd_4979212] using wordTrace_append hprefix tailTrace_4979212
  have hstable : (prefixWord ++ tailWord_4979212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4979212).length < 2 ^ (prefixWord ++ tailWord_4979212).sum := by decide
  have hdescent : baseEnd_4979212 < baseStart_4979212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4979212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4979269 : List Nat := [1, 3, 1, 1, 1, 6, 1, 4, 1, 1, 3]
def baseStart_4979269 : Nat := 118140960795 + 4979269 * 2 ^ 59
def prefixEnd_4979269 : Nat := 4983230072969 + 3 ^ 40 * 4979269 * 2
def baseEnd_4979269 : Nat := 2556758305032184320838265

theorem tailTrace_4979269 : CollatzResearch.WordTrace tailWord_4979269 prefixEnd_4979269 2556758305032184320838265 := by
  unfold tailWord_4979269
  simp only [CollatzResearch.WordTrace]
  refine ⟨181608860197966279287188861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121072573465310852858125907 181608860197966279287188861)
  ·
    refine ⟨68103322574237354732695823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181608860197966279287188861 68103322574237354732695823)
    ·
      refine ⟨102154983861356032099043735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68103322574237354732695823 102154983861356032099043735)
      ·
        refine ⟨153232475792034048148565603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102154983861356032099043735 153232475792034048148565603)
        ·
          refine ⟨229848713688051072222848405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153232475792034048148565603 229848713688051072222848405)
          ·
            refine ⟨10774158454127394010446019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 229848713688051072222848405 10774158454127394010446019)
            ·
              refine ⟨16161237681191091015669029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10774158454127394010446019 16161237681191091015669029)
              ·
                refine ⟨3030232065223329565437943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16161237681191091015669029 3030232065223329565437943)
                ·
                  refine ⟨4545348097834994348156915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3030232065223329565437943 4545348097834994348156915)
                  ·
                    refine ⟨6818022146752491522235373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4545348097834994348156915 6818022146752491522235373)
                    ·
                      refine ⟨2556758305032184320838265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6818022146752491522235373 2556758305032184320838265)
                      ·
                        rfl

theorem cell23_4979269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 4, 1, 1, 3].length) (baseStart_4979269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4979269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4979269 prefixEnd_4979269 := by exact prefixLift 4979269
  have htrace : WordTrace (prefixWord ++ tailWord_4979269) baseStart_4979269 baseEnd_4979269 := by
    simpa [prefixWord, tailWord_4979269, baseEnd_4979269] using wordTrace_append hprefix tailTrace_4979269
  have hstable : (prefixWord ++ tailWord_4979269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4979269).length < 2 ^ (prefixWord ++ tailWord_4979269).sum := by decide
  have hdescent : baseEnd_4979269 < baseStart_4979269 := by decide
  rcases family_descends (prefixWord ++ tailWord_4979269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4979288 : List Nat := [2, 1, 2, 2, 1, 2, 2, 3, 1, 1, 6]
def baseStart_4979288 : Nat := 118140960795 + 4979288 * 2 ^ 59
def prefixEnd_4979288 : Nat := 4983230072969 + 3 ^ 40 * 4979288 * 2
def baseEnd_4979288 : Nat := 2556768061164619746500677

theorem tailTrace_4979288 : CollatzResearch.WordTrace tailWord_4979288 prefixEnd_4979288 2556768061164619746500677 := by
  unfold tailWord_4979288
  simp only [CollatzResearch.WordTrace]
  refine ⟨90804776592448722766065259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121073035456598297021420345 90804776592448722766065259)
  ·
    refine ⟨136207164888673084149097889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90804776592448722766065259 136207164888673084149097889)
    ·
      refine ⟨102155373666504813111823417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136207164888673084149097889 102155373666504813111823417)
      ·
        refine ⟨76616530249878609833867563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102155373666504813111823417 76616530249878609833867563)
        ·
          refine ⟨114924795374817914750801345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76616530249878609833867563 114924795374817914750801345)
          ·
            refine ⟨86193596531113436063101009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114924795374817914750801345 86193596531113436063101009)
            ·
              refine ⟨64645197398335077047325757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86193596531113436063101009 64645197398335077047325757)
              ·
                refine ⟨24241949024375653892747159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64645197398335077047325757 24241949024375653892747159)
                ·
                  refine ⟨36362923536563480839120739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24241949024375653892747159 36362923536563480839120739)
                  ·
                    refine ⟨54544385304845221258681109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36362923536563480839120739 54544385304845221258681109)
                    ·
                      refine ⟨2556768061164619746500677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54544385304845221258681109 2556768061164619746500677)
                      ·
                        rfl

theorem cell23_4979288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_4979288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4979288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4979288 prefixEnd_4979288 := by exact prefixLift 4979288
  have htrace : WordTrace (prefixWord ++ tailWord_4979288) baseStart_4979288 baseEnd_4979288 := by
    simpa [prefixWord, tailWord_4979288, baseEnd_4979288] using wordTrace_append hprefix tailTrace_4979288
  have hstable : (prefixWord ++ tailWord_4979288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4979288).length < 2 ^ (prefixWord ++ tailWord_4979288).sum := by decide
  have hdescent : baseEnd_4979288 < baseStart_4979288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4979288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4979309 : List Nat := [1, 5, 1, 1, 3, 1, 4, 1, 1, 1, 4]
def baseStart_4979309 : Nat := 118140960795 + 4979309 * 2 ^ 59
def prefixEnd_4979309 : Nat := 4983230072969 + 3 ^ 40 * 4979309 * 2
def baseEnd_4979309 : Nat := 2556778844258364164338081

theorem tailTrace_4979309 : CollatzResearch.WordTrace tailWord_4979309 prefixEnd_4979309 2556778844258364164338081 := by
  unfold tailWord_4979309
  simp only [CollatzResearch.WordTrace]
  refine ⟨181610319117821366118644981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121073546078547577412429987 181610319117821366118644981)
  ·
    refine ⟨17025967417295753073622967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 181610319117821366118644981 17025967417295753073622967)
    ·
      refine ⟨25538951125943629610434451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17025967417295753073622967 25538951125943629610434451)
      ·
        refine ⟨38308426688915444415651677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25538951125943629610434451 38308426688915444415651677)
        ·
          refine ⟨14365660008343291655869379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38308426688915444415651677 14365660008343291655869379)
          ·
            refine ⟨21548490012514937483804069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14365660008343291655869379 21548490012514937483804069)
            ·
              refine ⟨4040341877346550778213263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21548490012514937483804069 4040341877346550778213263)
              ·
                refine ⟨6060512816019826167319895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4040341877346550778213263 6060512816019826167319895)
                ·
                  refine ⟨9090769224029739250979843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6060512816019826167319895 9090769224029739250979843)
                  ·
                    refine ⟨13636153836044608876469765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9090769224029739250979843 13636153836044608876469765)
                    ·
                      refine ⟨2556778844258364164338081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13636153836044608876469765 2556778844258364164338081)
                      ·
                        rfl

theorem cell23_4979309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 1, 1, 1, 4].length) (baseStart_4979309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4979309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4979309 prefixEnd_4979309 := by exact prefixLift 4979309
  have htrace : WordTrace (prefixWord ++ tailWord_4979309) baseStart_4979309 baseEnd_4979309 := by
    simpa [prefixWord, tailWord_4979309, baseEnd_4979309] using wordTrace_append hprefix tailTrace_4979309
  have hstable : (prefixWord ++ tailWord_4979309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4979309).length < 2 ^ (prefixWord ++ tailWord_4979309).sum := by decide
  have hdescent : baseEnd_4979309 < baseStart_4979309 := by decide
  rcases family_descends (prefixWord ++ tailWord_4979309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4979360 : List Nat := [2, 1, 1, 4, 5, 1, 1, 3, 1, 2, 2]
def baseStart_4979360 : Nat := 118140960795 + 4979360 * 2 ^ 59
def prefixEnd_4979360 : Nat := 4983230072969 + 3 ^ 40 * 4979360 * 2
def baseEnd_4979360 : Nat := 2556805031771743464800347

theorem tailTrace_4979360 : CollatzResearch.WordTrace tailWord_4979360 prefixEnd_4979360 2556805031771743464800347 := by
  unfold tailWord_4979360
  simp only [CollatzResearch.WordTrace]
  refine ⟨90806089620318300914375767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121074786160424401219167689 90806089620318300914375767)
  ·
    refine ⟨136209134430477451371563651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90806089620318300914375767 136209134430477451371563651)
    ·
      refine ⟨204313701645716177057345477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136209134430477451371563651 204313701645716177057345477)
      ·
        refine ⟨38308819058571783198252277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 204313701645716177057345477 38308819058571783198252277)
        ·
          refine ⟨3591451786741104674836151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38308819058571783198252277 3591451786741104674836151)
          ·
            refine ⟨5387177680111657012254227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3591451786741104674836151 5387177680111657012254227)
            ·
              refine ⟨8080766520167485518381341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5387177680111657012254227 8080766520167485518381341)
              ·
                refine ⟨3030287445062807069393003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8080766520167485518381341 3030287445062807069393003)
                ·
                  refine ⟨4545431167594210604089505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3030287445062807069393003 4545431167594210604089505)
                  ·
                    refine ⟨3409073375695657953067129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4545431167594210604089505 3409073375695657953067129)
                    ·
                      refine ⟨2556805031771743464800347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3409073375695657953067129 2556805031771743464800347)
                      ·
                        rfl

theorem cell23_4979360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 3, 1, 2, 2].length) (baseStart_4979360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4979360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4979360 prefixEnd_4979360 := by exact prefixLift 4979360
  have htrace : WordTrace (prefixWord ++ tailWord_4979360) baseStart_4979360 baseEnd_4979360 := by
    simpa [prefixWord, tailWord_4979360, baseEnd_4979360] using wordTrace_append hprefix tailTrace_4979360
  have hstable : (prefixWord ++ tailWord_4979360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4979360).length < 2 ^ (prefixWord ++ tailWord_4979360).sum := by decide
  have hdescent : baseEnd_4979360 < baseStart_4979360 := by decide
  rcases family_descends (prefixWord ++ tailWord_4979360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4979385 : List Nat := [1, 2, 1, 4, 1, 1, 1, 3, 2, 4, 3]
def baseStart_4979385 : Nat := 118140960795 + 4979385 * 2 ^ 59
def prefixEnd_4979385 : Nat := 4983230072969 + 3 ^ 40 * 4979385 * 2
def baseEnd_4979385 : Nat := 2556817868788105866987731

theorem tailTrace_4979385 : CollatzResearch.WordTrace tailWord_4979385 prefixEnd_4979385 2556817868788105866987731 := by
  unfold tailWord_4979385
  simp only [CollatzResearch.WordTrace]
  refine ⟨181613091065546031098411609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121075394043697354065607739 181613091065546031098411609)
  ·
    refine ⟨136209818299159523323808707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181613091065546031098411609 136209818299159523323808707)
    ·
      refine ⟨204314727448739284985713061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136209818299159523323808707 204314727448739284985713061)
      ·
        refine ⟨38309011396638615934821199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 204314727448739284985713061 38309011396638615934821199)
        ·
          refine ⟨57463517094957923902231799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38309011396638615934821199 57463517094957923902231799)
          ·
            refine ⟨86195275642436885853347699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57463517094957923902231799 86195275642436885853347699)
            ·
              refine ⟨129292913463655328780021549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86195275642436885853347699 129292913463655328780021549)
              ·
                refine ⟨48484842548870748292508081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 129292913463655328780021549 48484842548870748292508081)
                ·
                  refine ⟨36363631911653061219381061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48484842548870748292508081 36363631911653061219381061)
                  ·
                    refine ⟨6818180983434948978633949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36363631911653061219381061 6818180983434948978633949)
                    ·
                      refine ⟨2556817868788105866987731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6818180983434948978633949 2556817868788105866987731)
                      ·
                        rfl

theorem cell23_4979385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_4979385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4979385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4979385 prefixEnd_4979385 := by exact prefixLift 4979385
  have htrace : WordTrace (prefixWord ++ tailWord_4979385) baseStart_4979385 baseEnd_4979385 := by
    simpa [prefixWord, tailWord_4979385, baseEnd_4979385] using wordTrace_append hprefix tailTrace_4979385
  have hstable : (prefixWord ++ tailWord_4979385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4979385).length < 2 ^ (prefixWord ++ tailWord_4979385).sum := by decide
  have hdescent : baseEnd_4979385 < baseStart_4979385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4979385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4979393 : List Nat := [1, 2, 6, 2, 1, 1, 1, 3, 2, 1, 3]
def baseStart_4979393 : Nat := 118140960795 + 4979393 * 2 ^ 59
def prefixEnd_4979393 : Nat := 4983230072969 + 3 ^ 40 * 4979393 * 2
def baseEnd_4979393 : Nat := 2556821976633341835687695

theorem tailTrace_4979393 : CollatzResearch.WordTrace tailWord_4979393 prefixEnd_4979393 2556821976633341835687695 := by
  unfold tailWord_4979393
  simp only [CollatzResearch.WordTrace]
  refine ⟨181613382849517048464702833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121075588566344698976468555 181613382849517048464702833)
  ·
    refine ⟨136210037137137786348527125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181613382849517048464702833 136210037137137786348527125)
    ·
      refine ⟨6384845490803333735087209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 136210037137137786348527125 6384845490803333735087209)
      ·
        refine ⟨4788634118102500301315407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6384845490803333735087209 4788634118102500301315407)
        ·
          refine ⟨7182951177153750451973111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4788634118102500301315407 7182951177153750451973111)
          ·
            refine ⟨10774426765730625677959667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7182951177153750451973111 10774426765730625677959667)
            ·
              refine ⟨16161640148595938516939501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10774426765730625677959667 16161640148595938516939501)
              ·
                refine ⟨6060615055723476943852313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16161640148595938516939501 6060615055723476943852313)
                ·
                  refine ⟨4545461291792607707889235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6060615055723476943852313 4545461291792607707889235)
                  ·
                    refine ⟨6818191937688911561833853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4545461291792607707889235 6818191937688911561833853)
                    ·
                      refine ⟨2556821976633341835687695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6818191937688911561833853 2556821976633341835687695)
                      ·
                        rfl

theorem cell23_4979393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_4979393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4979393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4979393 prefixEnd_4979393 := by exact prefixLift 4979393
  have htrace : WordTrace (prefixWord ++ tailWord_4979393) baseStart_4979393 baseEnd_4979393 := by
    simpa [prefixWord, tailWord_4979393, baseEnd_4979393] using wordTrace_append hprefix tailTrace_4979393
  have hstable : (prefixWord ++ tailWord_4979393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4979393).length < 2 ^ (prefixWord ++ tailWord_4979393).sum := by decide
  have hdescent : baseEnd_4979393 < baseStart_4979393 := by decide
  rcases family_descends (prefixWord ++ tailWord_4979393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4979439 : List Nat := [1, 1, 2, 1, 5, 2, 4, 2, 5]
def baseStart_4979439 : Nat := 118140960795 + 4979439 * 2 ^ 59
def prefixEnd_4979439 : Nat := 4983230072969 + 3 ^ 40 * 4979439 * 2
def baseEnd_4979439 : Nat := 284093955193716517301387

theorem tailTrace_4979439 : CollatzResearch.WordTrace tailWord_4979439 prefixEnd_4979439 284093955193716517301387 := by
  unfold tailWord_4979439
  simp only [CollatzResearch.WordTrace]
  refine ⟨181615060607350398320877371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121076707071566932213918247 181615060607350398320877371)
  ·
    refine ⟨272422590911025597481316057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181615060607350398320877371 272422590911025597481316057)
    ·
      refine ⟨204316943183269198110987043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 272422590911025597481316057 204316943183269198110987043)
      ·
        refine ⟨306475414774903797166480565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204316943183269198110987043 306475414774903797166480565)
        ·
          refine ⟨28732070135147230984357553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 306475414774903797166480565 28732070135147230984357553)
          ·
            refine ⟨21549052601360423238268165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28732070135147230984357553 21549052601360423238268165)
            ·
              refine ⟨4040447362755079357175281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21549052601360423238268165 4040447362755079357175281)
              ·
                refine ⟨3030335522066309517881461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4040447362755079357175281 3030335522066309517881461)
                ·
                  refine ⟨284093955193716517301387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3030335522066309517881461 284093955193716517301387)
                  ·
                    rfl

theorem cell23_4979439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 2, 5].length) (baseStart_4979439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4979439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4979439 prefixEnd_4979439 := by exact prefixLift 4979439
  have htrace : WordTrace (prefixWord ++ tailWord_4979439) baseStart_4979439 baseEnd_4979439 := by
    simpa [prefixWord, tailWord_4979439, baseEnd_4979439] using wordTrace_append hprefix tailTrace_4979439
  have hstable : (prefixWord ++ tailWord_4979439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4979439).length < 2 ^ (prefixWord ++ tailWord_4979439).sum := by decide
  have hdescent : baseEnd_4979439 < baseStart_4979439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4979439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4979455 : List Nat := [1, 1, 2, 2, 1, 3, 1, 4, 1, 3, 4]
def baseStart_4979455 : Nat := 118140960795 + 4979455 * 2 ^ 59
def prefixEnd_4979455 : Nat := 4983230072969 + 3 ^ 40 * 4979455 * 2
def baseEnd_4979455 : Nat := 2556853812433920593112409

theorem tailTrace_4979455 : CollatzResearch.WordTrace tailWord_4979455 prefixEnd_4979455 2556853812433920593112409 := by
  unfold tailWord_4979455
  simp only [CollatzResearch.WordTrace]
  refine ⟨181615644175292433053459819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121077096116861622035639879 181615644175292433053459819)
  ·
    refine ⟨272423466262938649580189729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181615644175292433053459819 272423466262938649580189729)
    ·
      refine ⟨204317599697203987185142297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 272423466262938649580189729 204317599697203987185142297)
      ·
        refine ⟨153238199772902990388856723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204317599697203987185142297 153238199772902990388856723)
        ·
          refine ⟨229857299659354485583285085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153238199772902990388856723 229857299659354485583285085)
          ·
            refine ⟨86196487372257932093731907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 229857299659354485583285085 86196487372257932093731907)
            ·
              refine ⟨129294731058386898140597861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86196487372257932093731907 129294731058386898140597861)
              ·
                refine ⟨24242762073447543401362099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 129294731058386898140597861 24242762073447543401362099)
                ·
                  refine ⟨36364143110171315102043149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24242762073447543401362099 36364143110171315102043149)
                  ·
                    refine ⟨13636553666314243163266181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36364143110171315102043149 13636553666314243163266181)
                    ·
                      refine ⟨2556853812433920593112409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13636553666314243163266181 2556853812433920593112409)
                      ·
                        rfl

theorem cell23_4979455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 3, 4].length) (baseStart_4979455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4979455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4979455 prefixEnd_4979455 := by exact prefixLift 4979455
  have htrace : WordTrace (prefixWord ++ tailWord_4979455) baseStart_4979455 baseEnd_4979455 := by
    simpa [prefixWord, tailWord_4979455, baseEnd_4979455] using wordTrace_append hprefix tailTrace_4979455
  have hstable : (prefixWord ++ tailWord_4979455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4979455).length < 2 ^ (prefixWord ++ tailWord_4979455).sum := by decide
  have hdescent : baseEnd_4979455 < baseStart_4979455 := by decide
  rcases family_descends (prefixWord ++ tailWord_4979455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4979482 : List Nat := [3, 1, 1, 3, 2, 1, 1, 2, 5, 4]
def baseStart_4979482 : Nat := 118140960795 + 4979482 * 2 ^ 59
def prefixEnd_4979482 : Nat := 4983230072969 + 3 ^ 40 * 4979482 * 2
def baseEnd_4979482 : Nat := 852289225470530662491595

theorem tailTrace_4979482 : CollatzResearch.WordTrace tailWord_4979482 prefixEnd_4979482 852289225470530662491595 := by
  unfold tailWord_4979482
  simp only [CollatzResearch.WordTrace]
  refine ⟨45404157236548654166173175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121077752630796411109795133 45404157236548654166173175)
  ·
    refine ⟨68106235854822981249259763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45404157236548654166173175 68106235854822981249259763)
    ·
      refine ⟨102159353782234471873889645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68106235854822981249259763 102159353782234471873889645)
      ·
        refine ⟨38309757668337926952708617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102159353782234471873889645 38309757668337926952708617)
        ·
          refine ⟨28732318251253445214531463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38309757668337926952708617 28732318251253445214531463)
          ·
            refine ⟨43098477376880167821797195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28732318251253445214531463 43098477376880167821797195)
            ·
              refine ⟨64647716065320251732695793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43098477376880167821797195 64647716065320251732695793)
              ·
                refine ⟨48485787048990188799521845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64647716065320251732695793 48485787048990188799521845)
                ·
                  refine ⟨4545542535842830199955173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48485787048990188799521845 4545542535842830199955173)
                  ·
                    refine ⟨852289225470530662491595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4545542535842830199955173 852289225470530662491595)
                    ·
                      rfl

theorem cell23_4979482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 5, 4].length) (baseStart_4979482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4979482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4979482 prefixEnd_4979482 := by exact prefixLift 4979482
  have htrace : WordTrace (prefixWord ++ tailWord_4979482) baseStart_4979482 baseEnd_4979482 := by
    simpa [prefixWord, tailWord_4979482, baseEnd_4979482] using wordTrace_append hprefix tailTrace_4979482
  have hstable : (prefixWord ++ tailWord_4979482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4979482).length < 2 ^ (prefixWord ++ tailWord_4979482).sum := by decide
  have hdescent : baseEnd_4979482 < baseStart_4979482 := by decide
  rcases family_descends (prefixWord ++ tailWord_4979482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4979556 : List Nat := [2, 3, 1, 1, 4, 1, 3, 1, 3, 1, 3]
def baseStart_4979556 : Nat := 118140960795 + 4979556 * 2 ^ 59
def prefixEnd_4979556 : Nat := 4983230072969 + 3 ^ 40 * 4979556 * 2
def baseEnd_4979556 : Nat := 2556905673980024697949445

theorem tailTrace_4979556 : CollatzResearch.WordTrace tailWord_4979556 prefixEnd_4979556 2556905673980024697949445 := by
  unfold tailWord_4979556
  simp only [CollatzResearch.WordTrace]
  refine ⟨90809663973963263651443261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121079551965284351535257681 90809663973963263651443261)
  ·
    refine ⟨34053623990236223869291223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90809663973963263651443261 34053623990236223869291223)
    ·
      refine ⟨51080435985354335803936835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34053623990236223869291223 51080435985354335803936835)
      ·
        refine ⟨76620653978031503705905253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51080435985354335803936835 76620653978031503705905253)
        ·
          refine ⟨14366372620880906944857235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76620653978031503705905253 14366372620880906944857235)
          ·
            refine ⟨21549558931321360417285853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14366372620880906944857235 21549558931321360417285853)
            ·
              refine ⟨8081084599245510156482195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21549558931321360417285853 8081084599245510156482195)
              ·
                refine ⟨12121626898868265234723293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8081084599245510156482195 12121626898868265234723293)
                ·
                  refine ⟨4545610087075599463021235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12121626898868265234723293 4545610087075599463021235)
                  ·
                    refine ⟨6818415130613399194531853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4545610087075599463021235 6818415130613399194531853)
                    ·
                      refine ⟨2556905673980024697949445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6818415130613399194531853 2556905673980024697949445)
                      ·
                        rfl

theorem cell23_4979556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 1, 3, 1, 3].length) (baseStart_4979556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4979556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4979556 prefixEnd_4979556 := by exact prefixLift 4979556
  have htrace : WordTrace (prefixWord ++ tailWord_4979556) baseStart_4979556 baseEnd_4979556 := by
    simpa [prefixWord, tailWord_4979556, baseEnd_4979556] using wordTrace_append hprefix tailTrace_4979556
  have hstable : (prefixWord ++ tailWord_4979556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4979556).length < 2 ^ (prefixWord ++ tailWord_4979556).sum := by decide
  have hdescent : baseEnd_4979556 < baseStart_4979556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4979556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4979579 : List Nat := [1, 1, 1, 1, 1, 5, 5, 2, 1, 1, 4]
def baseStart_4979579 : Nat := 118140960795 + 4979579 * 2 ^ 59
def prefixEnd_4979579 : Nat := 4983230072969 + 3 ^ 40 * 4979579 * 2
def baseEnd_4979579 : Nat := 2556917484035078107961839

theorem tailTrace_4979579 : CollatzResearch.WordTrace tailWord_4979579 prefixEnd_4979579 2556917484035078107961839 := by
  unfold tailWord_4979579
  simp only [CollatzResearch.WordTrace]
  refine ⟨181620166826843202230973791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121080111217895468153982527 181620166826843202230973791)
  ·
    refine ⟨272430250240264803346460687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181620166826843202230973791 272430250240264803346460687)
    ·
      refine ⟨408645375360397205019691031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272430250240264803346460687 408645375360397205019691031)
      ·
        refine ⟨612968063040595807529536547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 408645375360397205019691031 612968063040595807529536547)
        ·
          refine ⟨919452094560893711294304821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 612968063040595807529536547 919452094560893711294304821)
          ·
            refine ⟨86198633865083785433841077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 919452094560893711294304821 86198633865083785433841077)
            ·
              refine ⟨8081121924851604884422601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 86198633865083785433841077 8081121924851604884422601)
              ·
                refine ⟨6060841443638703663316951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8081121924851604884422601 6060841443638703663316951)
                ·
                  refine ⟨9091262165458055494975427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6060841443638703663316951 9091262165458055494975427)
                  ·
                    refine ⟨13636893248187083242463141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9091262165458055494975427 13636893248187083242463141)
                    ·
                      refine ⟨2556917484035078107961839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13636893248187083242463141 2556917484035078107961839)
                      ·
                        rfl

theorem cell23_4979579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 2, 1, 1, 4].length) (baseStart_4979579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4979579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4979579 prefixEnd_4979579 := by exact prefixLift 4979579
  have htrace : WordTrace (prefixWord ++ tailWord_4979579) baseStart_4979579 baseEnd_4979579 := by
    simpa [prefixWord, tailWord_4979579, baseEnd_4979579] using wordTrace_append hprefix tailTrace_4979579
  have hstable : (prefixWord ++ tailWord_4979579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4979579).length < 2 ^ (prefixWord ++ tailWord_4979579).sum := by decide
  have hdescent : baseEnd_4979579 < baseStart_4979579 := by decide
  rcases family_descends (prefixWord ++ tailWord_4979579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4979602 : List Nat := [3, 2, 3, 2, 13]
def baseStart_4979602 : Nat := 118140960795 + 4979602 * 2 ^ 59
def prefixEnd_4979602 : Nat := 4983230072969 + 3 ^ 40 * 4979602 * 2
def baseEnd_4979602 : Nat := 3507447591344487678977

theorem tailTrace_4979602 : CollatzResearch.WordTrace tailWord_4979602 prefixEnd_4979602 3507447591344487678977 := by
  unfold tailWord_4979602
  simp only [CollatzResearch.WordTrace]
  refine ⟨45405251426439969289765265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121080670470506584772707373 45405251426439969289765265)
  ·
    refine ⟨34053938569829976967323949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45405251426439969289765265 34053938569829976967323949)
    ·
      refine ⟨12770226963686241362746481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34053938569829976967323949 12770226963686241362746481)
      ·
        refine ⟨9577670222764681022059861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12770226963686241362746481 9577670222764681022059861)
        ·
          refine ⟨3507447591344487678977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 9577670222764681022059861 3507447591344487678977)
          ·
            rfl

theorem cell23_4979602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 13].length) (baseStart_4979602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4979602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4979602 prefixEnd_4979602 := by exact prefixLift 4979602
  have htrace : WordTrace (prefixWord ++ tailWord_4979602) baseStart_4979602 baseEnd_4979602 := by
    simpa [prefixWord, tailWord_4979602, baseEnd_4979602] using wordTrace_append hprefix tailTrace_4979602
  have hstable : (prefixWord ++ tailWord_4979602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4979602).length < 2 ^ (prefixWord ++ tailWord_4979602).sum := by decide
  have hdescent : baseEnd_4979602 < baseStart_4979602 := by decide
  rcases family_descends (prefixWord ++ tailWord_4979602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4979642 : List Nat := [3, 1, 1, 1, 2, 1, 4, 1, 2, 2, 5]
def baseStart_4979642 : Nat := 118140960795 + 4979642 * 2 ^ 59
def prefixEnd_4979642 : Nat := 4983230072969 + 3 ^ 40 * 4979642 * 2
def baseEnd_4979642 : Nat := 2556949833316311361474049

theorem tailTrace_4979642 : CollatzResearch.WordTrace tailWord_4979642 prefixEnd_4979642 2556949833316311361474049 := by
  unfold tailWord_4979642
  simp only [CollatzResearch.WordTrace]
  refine ⟨45405616156403740997629295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121081643083743309327011453 45405616156403740997629295)
  ·
    refine ⟨68108424234605611496443943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45405616156403740997629295 68108424234605611496443943)
    ·
      refine ⟨102162636351908417244665915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68108424234605611496443943 102162636351908417244665915)
      ·
        refine ⟨153243954527862625866998873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102162636351908417244665915 153243954527862625866998873)
        ·
          refine ⟨114932965895896969400249155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153243954527862625866998873 114932965895896969400249155)
          ·
            refine ⟨172399448843845454100373733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114932965895896969400249155 172399448843845454100373733)
            ·
              refine ⟨32324896658221022643820075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 172399448843845454100373733 32324896658221022643820075)
              ·
                refine ⟨48487344987331533965730113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32324896658221022643820075 48487344987331533965730113)
                ·
                  refine ⟨36365508740498650474297585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48487344987331533965730113 36365508740498650474297585)
                  ·
                    refine ⟨27274131555373987855723189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36365508740498650474297585 27274131555373987855723189)
                    ·
                      refine ⟨2556949833316311361474049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27274131555373987855723189 2556949833316311361474049)
                      ·
                        rfl

theorem cell23_4979642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 2, 2, 5].length) (baseStart_4979642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4979642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4979642 prefixEnd_4979642 := by exact prefixLift 4979642
  have htrace : WordTrace (prefixWord ++ tailWord_4979642) baseStart_4979642 baseEnd_4979642 := by
    simpa [prefixWord, tailWord_4979642, baseEnd_4979642] using wordTrace_append hprefix tailTrace_4979642
  have hstable : (prefixWord ++ tailWord_4979642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4979642).length < 2 ^ (prefixWord ++ tailWord_4979642).sum := by decide
  have hdescent : baseEnd_4979642 < baseStart_4979642 := by decide
  rcases family_descends (prefixWord ++ tailWord_4979642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4979646 : List Nat := [4, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3]
def baseStart_4979646 : Nat := 118140960795 + 4979646 * 2 ^ 59
def prefixEnd_4979646 : Nat := 4983230072969 + 3 ^ 40 * 4979646 * 2
def baseEnd_4979646 : Nat := 2556951887238929345824031

theorem tailTrace_4979646 : CollatzResearch.WordTrace tailWord_4979646 prefixEnd_4979646 2556951887238929345824031 := by
  unfold tailWord_4979646
  simp only [CollatzResearch.WordTrace]
  refine ⟨22702826314700059084207849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121081740345066981782441861 22702826314700059084207849)
  ·
    refine ⟨17027119736025044313155887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22702826314700059084207849 17027119736025044313155887)
    ·
      refine ⟨25540679604037566469733831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17027119736025044313155887 25540679604037566469733831)
      ·
        refine ⟨38311019406056349704600747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25540679604037566469733831 38311019406056349704600747)
        ·
          refine ⟨57466529109084524556901121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38311019406056349704600747 57466529109084524556901121)
          ·
            refine ⟨43099896831813393417675841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57466529109084524556901121 43099896831813393417675841)
            ·
              refine ⟨32324922623860045063256881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43099896831813393417675841 32324922623860045063256881)
              ·
                refine ⟨24243691967895033797442661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32324922623860045063256881 24243691967895033797442661)
                ·
                  refine ⟨4545692243980318837020499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24243691967895033797442661 4545692243980318837020499)
                  ·
                    refine ⟨6818538365970478255530749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4545692243980318837020499 6818538365970478255530749)
                    ·
                      refine ⟨2556951887238929345824031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6818538365970478255530749 2556951887238929345824031)
                      ·
                        rfl

theorem cell23_4979646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3].length) (baseStart_4979646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4979646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4979646 prefixEnd_4979646 := by exact prefixLift 4979646
  have htrace : WordTrace (prefixWord ++ tailWord_4979646) baseStart_4979646 baseEnd_4979646 := by
    simpa [prefixWord, tailWord_4979646, baseEnd_4979646] using wordTrace_append hprefix tailTrace_4979646
  have hstable : (prefixWord ++ tailWord_4979646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4979646).length < 2 ^ (prefixWord ++ tailWord_4979646).sum := by decide
  have hdescent : baseEnd_4979646 < baseStart_4979646 := by decide
  rcases family_descends (prefixWord ++ tailWord_4979646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4979663 : List Nat := [1, 1, 2, 1, 1, 8, 1, 2, 2, 1, 3]
def baseStart_4979663 : Nat := 118140960795 + 4979663 * 2 ^ 59
def prefixEnd_4979663 : Nat := 4983230072969 + 3 ^ 40 * 4979663 * 2
def baseEnd_4979663 : Nat := 2556960616410055779311453

theorem tailTrace_4979663 : CollatzResearch.WordTrace tailWord_4979663 prefixEnd_4979663 2556960616410055779311453 := by
  unfold tailWord_4979663
  simp only [CollatzResearch.WordTrace]
  refine ⟨181623230558538884577031643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121082153705692589718021095 181623230558538884577031643)
  ·
    refine ⟨272434845837808326865547465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181623230558538884577031643 272434845837808326865547465)
    ·
      refine ⟨204326134378356245149160599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 272434845837808326865547465 204326134378356245149160599)
      ·
        refine ⟨306489201567534367723740899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204326134378356245149160599 306489201567534367723740899)
        ·
          refine ⟨459733802351301551585611349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 306489201567534367723740899 459733802351301551585611349)
          ·
            refine ⟨5387505496304315057643883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 459733802351301551585611349 5387505496304315057643883)
            ·
              refine ⟨8081258244456472586465825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5387505496304315057643883 8081258244456472586465825)
              ·
                refine ⟨6060943683342354439849369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8081258244456472586465825 6060943683342354439849369)
                ·
                  refine ⟨4545707762506765829887027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6060943683342354439849369 4545707762506765829887027)
                  ·
                    refine ⟨6818561643760148744830541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4545707762506765829887027 6818561643760148744830541)
                    ·
                      refine ⟨2556960616410055779311453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6818561643760148744830541 2556960616410055779311453)
                      ·
                        rfl

theorem cell23_4979663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 2, 2, 1, 3].length) (baseStart_4979663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4979663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4979663 prefixEnd_4979663 := by exact prefixLift 4979663
  have htrace : WordTrace (prefixWord ++ tailWord_4979663) baseStart_4979663 baseEnd_4979663 := by
    simpa [prefixWord, tailWord_4979663, baseEnd_4979663] using wordTrace_append hprefix tailTrace_4979663
  have hstable : (prefixWord ++ tailWord_4979663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4979663).length < 2 ^ (prefixWord ++ tailWord_4979663).sum := by decide
  have hdescent : baseEnd_4979663 < baseStart_4979663 := by decide
  rcases family_descends (prefixWord ++ tailWord_4979663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4979726 : List Nat := [4, 1, 1, 2, 2, 4, 1, 1, 7]
def baseStart_4979726 : Nat := 118140960795 + 4979726 * 2 ^ 59
def prefixEnd_4979726 : Nat := 4983230072969 + 3 ^ 40 * 4979726 * 2
def baseEnd_4979726 : Nat := 284110329521254336980407

theorem tailTrace_4979726 : CollatzResearch.WordTrace tailWord_4979726 prefixEnd_4979726 284110329521254336980407 := by
  unfold tailWord_4979726
  simp only [CollatzResearch.WordTrace]
  refine ⟨22703191044663830792071879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121083685571540430891050021 22703191044663830792071879)
  ·
    refine ⟨34054786566995746188107819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22703191044663830792071879 34054786566995746188107819)
    ·
      refine ⟨51082179850493619282161729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34054786566995746188107819 51082179850493619282161729)
      ·
        refine ⟨38311634887870214461621297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51082179850493619282161729 38311634887870214461621297)
        ·
          refine ⟨28733726165902660846215973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38311634887870214461621297 28733726165902660846215973)
          ·
            refine ⟨5387573656106748908665495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28733726165902660846215973 5387573656106748908665495)
            ·
              refine ⟨8081360484160123362998243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5387573656106748908665495 8081360484160123362998243)
              ·
                refine ⟨12122040726240185044497365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8081360484160123362998243 12122040726240185044497365)
                ·
                  refine ⟨284110329521254336980407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12122040726240185044497365 284110329521254336980407)
                  ·
                    rfl

theorem cell23_4979726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 1, 7].length) (baseStart_4979726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4979726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4979726 prefixEnd_4979726 := by exact prefixLift 4979726
  have htrace : WordTrace (prefixWord ++ tailWord_4979726) baseStart_4979726 baseEnd_4979726 := by
    simpa [prefixWord, tailWord_4979726, baseEnd_4979726] using wordTrace_append hprefix tailTrace_4979726
  have hstable : (prefixWord ++ tailWord_4979726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4979726).length < 2 ^ (prefixWord ++ tailWord_4979726).sum := by decide
  have hdescent : baseEnd_4979726 < baseStart_4979726 := by decide
  rcases family_descends (prefixWord ++ tailWord_4979726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4979766 : List Nat := [5, 1, 2, 1, 1, 2, 1, 2, 1, 2, 5]
def baseStart_4979766 : Nat := 118140960795 + 4979766 * 2 ^ 59
def prefixEnd_4979766 : Nat := 4983230072969 + 3 ^ 40 * 4979766 * 2
def baseEnd_4979766 : Nat := 2557013504917468876323479

theorem tailTrace_4979766 : CollatzResearch.WordTrace tailWord_4979766 prefixEnd_4979766 2557013504917468876323479 := by
  unfold tailWord_4979766
  simp only [CollatzResearch.WordTrace]
  refine ⟨11351686704822858323001947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 121084658184777155445354101 11351686704822858323001947)
  ·
    refine ⟨17027530057234287484502921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11351686704822858323001947 17027530057234287484502921)
    ·
      refine ⟨12770647542925715613377191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17027530057234287484502921 12770647542925715613377191)
      ·
        refine ⟨19155971314388573420065787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12770647542925715613377191 19155971314388573420065787)
        ·
          refine ⟨28733956971582860130098681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19155971314388573420065787 28733956971582860130098681)
          ·
            refine ⟨21550467728687145097574011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28733956971582860130098681 21550467728687145097574011)
            ·
              refine ⟨32325701593030717646361017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21550467728687145097574011 32325701593030717646361017)
              ·
                refine ⟨24244276194773038234770763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32325701593030717646361017 24244276194773038234770763)
                ·
                  refine ⟨36366414292159557352156145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24244276194773038234770763 36366414292159557352156145)
                  ·
                    refine ⟨27274810719119668014117109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36366414292159557352156145 27274810719119668014117109)
                    ·
                      refine ⟨2557013504917468876323479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27274810719119668014117109 2557013504917468876323479)
                      ·
                        rfl

theorem cell23_4979766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_4979766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4979766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4979766 prefixEnd_4979766 := by exact prefixLift 4979766
  have htrace : WordTrace (prefixWord ++ tailWord_4979766) baseStart_4979766 baseEnd_4979766 := by
    simpa [prefixWord, tailWord_4979766, baseEnd_4979766] using wordTrace_append hprefix tailTrace_4979766
  have hstable : (prefixWord ++ tailWord_4979766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4979766).length < 2 ^ (prefixWord ++ tailWord_4979766).sum := by decide
  have hdescent : baseEnd_4979766 < baseStart_4979766 := by decide
  rcases family_descends (prefixWord ++ tailWord_4979766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4979776 : List Nat := [2, 1, 1, 2, 2, 3, 2, 2, 2, 4, 2]
def baseStart_4979776 : Nat := 118140960795 + 4979776 * 2 ^ 59
def prefixEnd_4979776 : Nat := 4983230072969 + 3 ^ 40 * 4979776 * 2
def baseEnd_4979776 : Nat := 2557018639724013837198433

theorem tailTrace_4979776 : CollatzResearch.WordTrace tailWord_4979776 prefixEnd_4979776 2557018639724013837198433 := by
  unfold tailWord_4979776
  simp only [CollatzResearch.WordTrace]
  refine ⟨90813676003564752437947591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121084901338086336583930121 90813676003564752437947591)
  ·
    refine ⟨136220514005347128656921387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90813676003564752437947591 136220514005347128656921387)
    ·
      refine ⟨204330771008020692985382081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136220514005347128656921387 204330771008020692985382081)
      ·
        refine ⟨153248078256015519739036561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204330771008020692985382081 153248078256015519739036561)
        ·
          refine ⟨114936058692011639804277421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153248078256015519739036561 114936058692011639804277421)
          ·
            refine ⟨43101022009504364926604033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114936058692011639804277421 43101022009504364926604033)
            ·
              refine ⟨32325766507128273694953025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43101022009504364926604033 32325766507128273694953025)
              ·
                refine ⟨24244324880346205271214769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32325766507128273694953025 24244324880346205271214769)
                ·
                  refine ⟨18183243660259653953411077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24244324880346205271214769 18183243660259653953411077)
                  ·
                    refine ⟨3409358186298685116264577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18183243660259653953411077 3409358186298685116264577)
                    ·
                      refine ⟨2557018639724013837198433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3409358186298685116264577 2557018639724013837198433)
                      ·
                        rfl

theorem cell23_4979776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 2, 4, 2].length) (baseStart_4979776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4979776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4979776 prefixEnd_4979776 := by exact prefixLift 4979776
  have htrace : WordTrace (prefixWord ++ tailWord_4979776) baseStart_4979776 baseEnd_4979776 := by
    simpa [prefixWord, tailWord_4979776, baseEnd_4979776] using wordTrace_append hprefix tailTrace_4979776
  have hstable : (prefixWord ++ tailWord_4979776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4979776).length < 2 ^ (prefixWord ++ tailWord_4979776).sum := by decide
  have hdescent : baseEnd_4979776 < baseStart_4979776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4979776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4979777 : List Nat := [1, 2, 5, 1, 4, 1, 2, 2, 5]
def baseStart_4979777 : Nat := 118140960795 + 4979777 * 2 ^ 59
def prefixEnd_4979777 : Nat := 4983230072969 + 3 ^ 40 * 4979777 * 2
def baseEnd_4979777 : Nat := 284113239244963148142881

theorem tailTrace_4979777 : CollatzResearch.WordTrace tailWord_4979777 prefixEnd_4979777 284113239244963148142881 := by
  unfold tailWord_4979777
  simp only [CollatzResearch.WordTrace]
  refine ⟨181627388480125882046681585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121084925653417254697787723 181627388480125882046681585)
  ·
    refine ⟨136220541360094411535011189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181627388480125882046681585 136220541360094411535011189)
    ·
      refine ⟨12770675752508851081407299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 136220541360094411535011189 12770675752508851081407299)
      ·
        refine ⟨19156013628763276622110949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12770675752508851081407299 19156013628763276622110949)
        ·
          refine ⟨3591752555393114366645803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19156013628763276622110949 3591752555393114366645803)
          ·
            refine ⟨5387628833089671549968705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3591752555393114366645803 5387628833089671549968705)
            ·
              refine ⟨4040721624817253662476529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5387628833089671549968705 4040721624817253662476529)
              ·
                refine ⟨3030541218612940246857397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4040721624817253662476529 3030541218612940246857397)
                ·
                  refine ⟨284113239244963148142881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3030541218612940246857397 284113239244963148142881)
                  ·
                    rfl

theorem cell23_4979777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 2, 5].length) (baseStart_4979777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4979777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4979777 prefixEnd_4979777 := by exact prefixLift 4979777
  have htrace : WordTrace (prefixWord ++ tailWord_4979777) baseStart_4979777 baseEnd_4979777 := by
    simpa [prefixWord, tailWord_4979777, baseEnd_4979777] using wordTrace_append hprefix tailTrace_4979777
  have hstable : (prefixWord ++ tailWord_4979777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4979777).length < 2 ^ (prefixWord ++ tailWord_4979777).sum := by decide
  have hdescent : baseEnd_4979777 < baseStart_4979777 := by decide
  rcases family_descends (prefixWord ++ tailWord_4979777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4979796 : List Nat := [2, 4, 1, 1, 1, 1, 2, 2, 4, 2, 3]
def baseStart_4979796 : Nat := 118140960795 + 4979796 * 2 ^ 59
def prefixEnd_4979796 : Nat := 4983230072969 + 3 ^ 40 * 4979796 * 2
def baseEnd_4979796 : Nat := 2557028909337103758948341

theorem tailTrace_4979796 : CollatzResearch.WordTrace tailWord_4979796 prefixEnd_4979796 2557028909337103758948341 := by
  unfold tailWord_4979796
  simp only [CollatzResearch.WordTrace]
  refine ⟨90814040733528524145811621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121085387644704698861082161 90814040733528524145811621)
  ·
    refine ⟨17027632637536598277339679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90814040733528524145811621 17027632637536598277339679)
    ·
      refine ⟨25541448956304897416009519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17027632637536598277339679 25541448956304897416009519)
      ·
        refine ⟨38312173434457346124014279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25541448956304897416009519 38312173434457346124014279)
        ·
          refine ⟨57468260151686019186021419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38312173434457346124014279 57468260151686019186021419)
          ·
            refine ⟨86202390227529028779032129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57468260151686019186021419 86202390227529028779032129)
            ·
              refine ⟨64651792670646771584274097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86202390227529028779032129 64651792670646771584274097)
              ·
                refine ⟨48488844502985078688205573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64651792670646771584274097 48488844502985078688205573)
                ·
                  refine ⟨9091658344309702254038545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48488844502985078688205573 9091658344309702254038545)
                  ·
                    refine ⟨6818743758232276690528909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9091658344309702254038545 6818743758232276690528909)
                    ·
                      refine ⟨2557028909337103758948341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6818743758232276690528909 2557028909337103758948341)
                      ·
                        rfl

theorem cell23_4979796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_4979796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4979796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4979796 prefixEnd_4979796 := by exact prefixLift 4979796
  have htrace : WordTrace (prefixWord ++ tailWord_4979796) baseStart_4979796 baseEnd_4979796 := by
    simpa [prefixWord, tailWord_4979796, baseEnd_4979796] using wordTrace_append hprefix tailTrace_4979796
  have hstable : (prefixWord ++ tailWord_4979796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4979796).length < 2 ^ (prefixWord ++ tailWord_4979796).sum := by decide
  have hdescent : baseEnd_4979796 < baseStart_4979796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4979796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4979810 : List Nat := [3, 3, 2, 2, 1, 3, 1, 1, 2, 1, 4]
def baseStart_4979810 : Nat := 118140960795 + 4979810 * 2 ^ 59
def prefixEnd_4979810 : Nat := 4983230072969 + 3 ^ 40 * 4979810 * 2
def baseEnd_4979810 : Nat := 2557036098066266704173277

theorem tailTrace_4979810 : CollatzResearch.WordTrace tailWord_4979810 prefixEnd_4979810 2557036098066266704173277 := by
  unfold tailWord_4979810
  simp only [CollatzResearch.WordTrace]
  refine ⟨45407148022251582170658221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121085728059337552455088589 45407148022251582170658221)
  ·
    refine ⟨17027680508344343313996833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45407148022251582170658221 17027680508344343313996833)
    ·
      refine ⟨12770760381258257485497625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17027680508344343313996833 12770760381258257485497625)
      ·
        refine ⟨9578070285943693114123219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12770760381258257485497625 9578070285943693114123219)
        ·
          refine ⟨14367105428915539671184829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9578070285943693114123219 14367105428915539671184829)
          ·
            refine ⟨5387664535843327376694311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14367105428915539671184829 5387664535843327376694311)
            ·
              refine ⟨8081496803764991065041467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5387664535843327376694311 8081496803764991065041467)
              ·
                refine ⟨12122245205647486597562201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8081496803764991065041467 12122245205647486597562201)
                ·
                  refine ⟨9091683904235614948171651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12122245205647486597562201 9091683904235614948171651)
                  ·
                    refine ⟨13637525856353422422257477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9091683904235614948171651 13637525856353422422257477)
                    ·
                      refine ⟨2557036098066266704173277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13637525856353422422257477 2557036098066266704173277)
                      ·
                        rfl

theorem cell23_4979810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_4979810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4979810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4979810 prefixEnd_4979810 := by exact prefixLift 4979810
  have htrace : WordTrace (prefixWord ++ tailWord_4979810) baseStart_4979810 baseEnd_4979810 := by
    simpa [prefixWord, tailWord_4979810, baseEnd_4979810] using wordTrace_append hprefix tailTrace_4979810
  have hstable : (prefixWord ++ tailWord_4979810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4979810).length < 2 ^ (prefixWord ++ tailWord_4979810).sum := by decide
  have hdescent : baseEnd_4979810 < baseStart_4979810 := by decide
  rcases family_descends (prefixWord ++ tailWord_4979810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4979833 : List Nat := [1, 2, 1, 3, 5, 2, 1, 2, 6]
def baseStart_4979833 : Nat := 118140960795 + 4979833 * 2 ^ 59
def prefixEnd_4979833 : Nat := 4983230072969 + 3 ^ 40 * 4979833 * 2
def baseEnd_4979833 : Nat := 284116434235702234909519

theorem tailTrace_4979833 : CollatzResearch.WordTrace tailWord_4979833 prefixEnd_4979833 284116434235702234909519 := by
  unfold tailWord_4979833
  simp only [CollatzResearch.WordTrace]
  refine ⟨181629430967923003610720153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121086287311948669073813435 181629430967923003610720153)
  ·
    refine ⟨136222073225942252708040115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181629430967923003610720153 136222073225942252708040115)
    ·
      refine ⟨204333109838913379062060173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136222073225942252708040115 204333109838913379062060173)
      ·
        refine ⟨76624916189592517148272565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 204333109838913379062060173 76624916189592517148272565)
        ·
          refine ⟨7183585892774298482650553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76624916189592517148272565 7183585892774298482650553)
          ·
            refine ⟨5387689419580723861987915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7183585892774298482650553 5387689419580723861987915)
            ·
              refine ⟨8081534129371085792981873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5387689419580723861987915 8081534129371085792981873)
              ·
                refine ⟨6061150597028314344736405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8081534129371085792981873 6061150597028314344736405)
                ·
                  refine ⟨284116434235702234909519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6061150597028314344736405 284116434235702234909519)
                  ·
                    rfl

theorem cell23_4979833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 2, 6].length) (baseStart_4979833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4979833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4979833 prefixEnd_4979833 := by exact prefixLift 4979833
  have htrace : WordTrace (prefixWord ++ tailWord_4979833) baseStart_4979833 baseEnd_4979833 := by
    simpa [prefixWord, tailWord_4979833, baseEnd_4979833] using wordTrace_append hprefix tailTrace_4979833
  have hstable : (prefixWord ++ tailWord_4979833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4979833).length < 2 ^ (prefixWord ++ tailWord_4979833).sum := by decide
  have hdescent : baseEnd_4979833 < baseStart_4979833 := by decide
  rcases family_descends (prefixWord ++ tailWord_4979833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4979843 : List Nat := [1, 1, 1, 3, 3, 2, 4, 1, 3, 1, 3]
def baseStart_4979843 : Nat := 118140960795 + 4979843 * 2 ^ 59
def prefixEnd_4979843 : Nat := 4983230072969 + 3 ^ 40 * 4979843 * 2
def baseEnd_4979843 : Nat := 2557053042927865075060625

theorem tailTrace_4979843 : CollatzResearch.WordTrace tailWord_4979843 prefixEnd_4979843 2557053042927865075060625 := by
  unfold tailWord_4979843
  simp only [CollatzResearch.WordTrace]
  refine ⟨181629795697886775318584183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121086530465257850212389455 181629795697886775318584183)
  ·
    refine ⟨272444693546830162977876275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181629795697886775318584183 272444693546830162977876275)
    ·
      refine ⟨408667040320245244466814413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272444693546830162977876275 408667040320245244466814413)
      ·
        refine ⟨153250140120091966675055405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 408667040320245244466814413 153250140120091966675055405)
        ·
          refine ⟨57468802545034487503145777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153250140120091966675055405 57468802545034487503145777)
          ·
            refine ⟨43101601908775865627359333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57468802545034487503145777 43101601908775865627359333)
            ·
              refine ⟨8081550357895474805129875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43101601908775865627359333 8081550357895474805129875)
              ·
                refine ⟨12122325536843212207694813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8081550357895474805129875 12122325536843212207694813)
                ·
                  refine ⟨4545872076316204577885555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12122325536843212207694813 4545872076316204577885555)
                  ·
                    refine ⟨6818808114474306866828333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4545872076316204577885555 6818808114474306866828333)
                    ·
                      refine ⟨2557053042927865075060625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6818808114474306866828333 2557053042927865075060625)
                      ·
                        rfl

theorem cell23_4979843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 1, 3, 1, 3].length) (baseStart_4979843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4979843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4979843 prefixEnd_4979843 := by exact prefixLift 4979843
  have htrace : WordTrace (prefixWord ++ tailWord_4979843) baseStart_4979843 baseEnd_4979843 := by
    simpa [prefixWord, tailWord_4979843, baseEnd_4979843] using wordTrace_append hprefix tailTrace_4979843
  have hstable : (prefixWord ++ tailWord_4979843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4979843).length < 2 ^ (prefixWord ++ tailWord_4979843).sum := by decide
  have hdescent : baseEnd_4979843 < baseStart_4979843 := by decide
  rcases family_descends (prefixWord ++ tailWord_4979843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4979863 : List Nat := [1, 1, 3, 3, 3, 2, 2, 2, 1, 5]
def baseStart_4979863 : Nat := 118140960795 + 4979863 * 2 ^ 59
def prefixEnd_4979863 : Nat := 4983230072969 + 3 ^ 40 * 4979863 * 2
def baseEnd_4979863 : Nat := 852354437513651665603511

theorem tailTrace_4979863 : CollatzResearch.WordTrace tailWord_4979863 prefixEnd_4979863 852354437513651665603511 := by
  unfold tailWord_4979863
  simp only [CollatzResearch.WordTrace]
  refine ⟨181630525157814318734312243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121087016771876212489541495 181630525157814318734312243)
  ·
    refine ⟨272445787736721478101468365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181630525157814318734312243 272445787736721478101468365)
    ·
      refine ⟨102167170401270554288050637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 272445787736721478101468365 102167170401270554288050637)
      ·
        refine ⟨38312688900476457858018989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102167170401270554288050637 38312688900476457858018989)
        ·
          refine ⟨14367258337678671696757121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38312688900476457858018989 14367258337678671696757121)
          ·
            refine ⟨10775443753259003772567841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14367258337678671696757121 10775443753259003772567841)
            ·
              refine ⟨8081582814944252829425881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10775443753259003772567841 8081582814944252829425881)
              ·
                refine ⟨6061187111208189622069411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8081582814944252829425881 6061187111208189622069411)
                ·
                  refine ⟨9091780666812284433104117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6061187111208189622069411 9091780666812284433104117)
                  ·
                    refine ⟨852354437513651665603511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9091780666812284433104117 852354437513651665603511)
                    ·
                      rfl

theorem cell23_4979863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 2, 1, 5].length) (baseStart_4979863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4979863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4979863 prefixEnd_4979863 := by exact prefixLift 4979863
  have htrace : WordTrace (prefixWord ++ tailWord_4979863) baseStart_4979863 baseEnd_4979863 := by
    simpa [prefixWord, tailWord_4979863, baseEnd_4979863] using wordTrace_append hprefix tailTrace_4979863
  have hstable : (prefixWord ++ tailWord_4979863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4979863).length < 2 ^ (prefixWord ++ tailWord_4979863).sum := by decide
  have hdescent : baseEnd_4979863 < baseStart_4979863 := by decide
  rcases family_descends (prefixWord ++ tailWord_4979863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4979870 : List Nat := [4, 3, 1, 1, 2, 1, 2, 1, 1, 5, 2]
def baseStart_4979870 : Nat := 118140960795 + 4979870 * 2 ^ 59
def prefixEnd_4979870 : Nat := 4983230072969 + 3 ^ 40 * 4979870 * 2
def baseEnd_4979870 : Nat := 2557066906905536469423001

theorem tailTrace_4979870 : CollatzResearch.WordTrace tailWord_4979870 prefixEnd_4979870 2557066906905536469423001 := by
  unfold tailWord_4979870
  simp only [CollatzResearch.WordTrace]
  refine ⟨22703847558598619866227133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121087186979192639286544709 22703847558598619866227133)
  ·
    refine ⟨8513942834474482449835175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22703847558598619866227133 8513942834474482449835175)
    ·
      refine ⟨12770914251711723674752763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8513942834474482449835175 12770914251711723674752763)
      ·
        refine ⟨19156371377567585512129145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12770914251711723674752763 19156371377567585512129145)
        ·
          refine ⟨14367278533175689134096859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19156371377567585512129145 14367278533175689134096859)
          ·
            refine ⟨21550917799763533701145289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14367278533175689134096859 21550917799763533701145289)
            ·
              refine ⟨16163188349822650275858967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21550917799763533701145289 16163188349822650275858967)
              ·
                refine ⟨24244782524733975413788451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16163188349822650275858967 24244782524733975413788451)
                ·
                  refine ⟨36367173787100963120682677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24244782524733975413788451 36367173787100963120682677)
                  ·
                    refine ⟨3409422542540715292564001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36367173787100963120682677 3409422542540715292564001)
                    ·
                      refine ⟨2557066906905536469423001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3409422542540715292564001 2557066906905536469423001)
                      ·
                        rfl

theorem cell23_4979870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_4979870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4979870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4979870 prefixEnd_4979870 := by exact prefixLift 4979870
  have htrace : WordTrace (prefixWord ++ tailWord_4979870) baseStart_4979870 baseEnd_4979870 := by
    simpa [prefixWord, tailWord_4979870, baseEnd_4979870] using wordTrace_append hprefix tailTrace_4979870
  have hstable : (prefixWord ++ tailWord_4979870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4979870).length < 2 ^ (prefixWord ++ tailWord_4979870).sum := by decide
  have hdescent : baseEnd_4979870 < baseStart_4979870 := by decide
  rcases family_descends (prefixWord ++ tailWord_4979870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4979877 : List Nat := [1, 3, 1, 2, 1, 6, 1, 3, 1, 1, 3]
def baseStart_4979877 : Nat := 118140960795 + 4979877 * 2 ^ 59
def prefixEnd_4979877 : Nat := 4983230072969 + 3 ^ 40 * 4979877 * 2
def baseEnd_4979877 : Nat := 2557070501270117942035469

theorem tailTrace_4979877 : CollatzResearch.WordTrace tailWord_4979877 prefixEnd_4979877 2557070501270117942035469 := by
  unfold tailWord_4979877
  simp only [CollatzResearch.WordTrace]
  refine ⟨181631035779763599125321885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121087357186509066083547923 181631035779763599125321885)
  ·
    refine ⟨68111638417411349671995707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181631035779763599125321885 68111638417411349671995707)
    ·
      refine ⟨102167457626117024507993561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68111638417411349671995707 102167457626117024507993561)
      ·
        refine ⟨76625593219587768380995171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102167457626117024507993561 76625593219587768380995171)
        ·
          refine ⟨114938389829381652571492757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76625593219587768380995171 114938389829381652571492757)
          ·
            refine ⟨5387737023252264964288723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 114938389829381652571492757 5387737023252264964288723)
            ·
              refine ⟨8081605534878397446433085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5387737023252264964288723 8081605534878397446433085)
              ·
                refine ⟨3030602075579399042412407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8081605534878397446433085 3030602075579399042412407)
                ·
                  refine ⟨4545903113369098563618611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3030602075579399042412407 4545903113369098563618611)
                  ·
                    refine ⟨6818854670053647845427917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4545903113369098563618611 6818854670053647845427917)
                    ·
                      refine ⟨2557070501270117942035469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6818854670053647845427917 2557070501270117942035469)
                      ·
                        rfl

theorem cell23_4979877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 3, 1, 1, 3].length) (baseStart_4979877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4979877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4979877 prefixEnd_4979877 := by exact prefixLift 4979877
  have htrace : WordTrace (prefixWord ++ tailWord_4979877) baseStart_4979877 baseEnd_4979877 := by
    simpa [prefixWord, tailWord_4979877, baseEnd_4979877] using wordTrace_append hprefix tailTrace_4979877
  have hstable : (prefixWord ++ tailWord_4979877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4979877).length < 2 ^ (prefixWord ++ tailWord_4979877).sum := by decide
  have hdescent : baseEnd_4979877 < baseStart_4979877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4979877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4979909 : List Nat := [1, 3, 1, 1, 1, 1, 3, 1, 1, 4, 6]
def baseStart_4979909 : Nat := 118140960795 + 4979909 * 2 ^ 59
def prefixEnd_4979909 : Nat := 4983230072969 + 3 ^ 40 * 4979909 * 2
def baseEnd_4979909 : Nat := 2557086932651061816835321

theorem tailTrace_4979909 : CollatzResearch.WordTrace tailWord_4979909 prefixEnd_4979909 2557086932651061816835321 := by
  unfold tailWord_4979909
  simp only [CollatzResearch.WordTrace]
  refine ⟨181632202915647668590486781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121088135277098445726991187 181632202915647668590486781)
  ·
    refine ⟨68112076093367875721432543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181632202915647668590486781 68112076093367875721432543)
    ·
      refine ⟨102168114140051813582148815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68112076093367875721432543 102168114140051813582148815)
      ·
        refine ⟨153252171210077720373223223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102168114140051813582148815 153252171210077720373223223)
        ·
          refine ⟨229878256815116580559834835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153252171210077720373223223 229878256815116580559834835)
          ·
            refine ⟨344817385222674870839752253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229878256815116580559834835 344817385222674870839752253)
            ·
              refine ⟨129306519458503076564907095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 344817385222674870839752253 129306519458503076564907095)
              ·
                refine ⟨193959779187754614847360643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129306519458503076564907095 193959779187754614847360643)
                ·
                  refine ⟨290939668781631922271040965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 193959779187754614847360643 290939668781631922271040965)
                  ·
                    refine ⟨54551187896555985425820181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 290939668781631922271040965 54551187896555985425820181)
                    ·
                      refine ⟨2557086932651061816835321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54551187896555985425820181 2557086932651061816835321)
                      ·
                        rfl

theorem cell23_4979909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 4, 6].length) (baseStart_4979909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4979909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4979909 prefixEnd_4979909 := by exact prefixLift 4979909
  have htrace : WordTrace (prefixWord ++ tailWord_4979909) baseStart_4979909 baseEnd_4979909 := by
    simpa [prefixWord, tailWord_4979909, baseEnd_4979909] using wordTrace_append hprefix tailTrace_4979909
  have hstable : (prefixWord ++ tailWord_4979909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4979909).length < 2 ^ (prefixWord ++ tailWord_4979909).sum := by decide
  have hdescent : baseEnd_4979909 < baseStart_4979909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4979909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4979917 : List Nat := [1, 6, 2, 2, 1, 1, 1, 1, 3, 1, 4]
def baseStart_4979917 : Nat := 118140960795 + 4979917 * 2 ^ 59
def prefixEnd_4979917 : Nat := 4983230072969 + 3 ^ 40 * 4979917 * 2
def baseEnd_4979917 : Nat := 2557091040496297785535285

theorem tailTrace_4979917 : CollatzResearch.WordTrace tailWord_4979917 prefixEnd_4979917 2557091040496297785535285 := by
  unfold tailWord_4979917
  simp only [CollatzResearch.WordTrace]
  refine ⟨181632494699618685956778005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121088329799745790637852003 181632494699618685956778005)
  ·
    refine ⟨8514023189044625904223969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 181632494699618685956778005 8514023189044625904223969)
    ·
      refine ⟨6385517391783469428167977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8514023189044625904223969 6385517391783469428167977)
      ·
        refine ⟨4789138043837602071125983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6385517391783469428167977 4789138043837602071125983)
        ·
          refine ⟨7183707065756403106688975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4789138043837602071125983 7183707065756403106688975)
          ·
            refine ⟨10775560598634604660033463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7183707065756403106688975 10775560598634604660033463)
            ·
              refine ⟨16163340897951906990050195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10775560598634604660033463 16163340897951906990050195)
              ·
                refine ⟨24245011346927860485075293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16163340897951906990050195 24245011346927860485075293)
                ·
                  refine ⟨9091879255097947681903235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24245011346927860485075293 9091879255097947681903235)
                  ·
                    refine ⟨13637818882646921522854853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9091879255097947681903235 13637818882646921522854853)
                    ·
                      refine ⟨2557091040496297785535285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13637818882646921522854853 2557091040496297785535285)
                      ·
                        rfl

theorem cell23_4979917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_4979917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4979917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4979917 prefixEnd_4979917 := by exact prefixLift 4979917
  have htrace : WordTrace (prefixWord ++ tailWord_4979917) baseStart_4979917 baseEnd_4979917 := by
    simpa [prefixWord, tailWord_4979917, baseEnd_4979917] using wordTrace_append hprefix tailTrace_4979917
  have hstable : (prefixWord ++ tailWord_4979917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4979917).length < 2 ^ (prefixWord ++ tailWord_4979917).sum := by decide
  have hdescent : baseEnd_4979917 < baseStart_4979917 := by decide
  rcases family_descends (prefixWord ++ tailWord_4979917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4979919 : List Nat := [1, 1, 2, 1, 1, 3, 2, 1, 4, 7]
def baseStart_4979919 : Nat := 118140960795 + 4979919 * 2 ^ 59
def prefixEnd_4979919 : Nat := 4983230072969 + 3 ^ 40 * 4979919 * 2
def baseEnd_4979919 : Nat := 852364022485868925903425

theorem tailTrace_4979919 : CollatzResearch.WordTrace tailWord_4979919 prefixEnd_4979919 852364022485868925903425 := by
  unfold tailWord_4979919
  simp only [CollatzResearch.WordTrace]
  refine ⟨181632567645611440298350811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121088378430407626865567207 181632567645611440298350811)
  ·
    refine ⟨272448851468417160447526217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181632567645611440298350811 272448851468417160447526217)
    ·
      refine ⟨204336638601312870335644663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 272448851468417160447526217 204336638601312870335644663)
      ·
        refine ⟨306504957901969305503466995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204336638601312870335644663 306504957901969305503466995)
        ·
          refine ⟨459757436852953958255200493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 306504957901969305503466995 459757436852953958255200493)
          ·
            refine ⟨172409038819857734345700185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 459757436852953958255200493 172409038819857734345700185)
            ·
              refine ⟨129306779114893300759275139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 172409038819857734345700185 129306779114893300759275139)
              ·
                refine ⟨193960168672339951138912709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129306779114893300759275139 193960168672339951138912709)
                ·
                  refine ⟨36367531626063740838546133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 193960168672339951138912709 36367531626063740838546133)
                  ·
                    refine ⟨852364022485868925903425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36367531626063740838546133 852364022485868925903425)
                    ·
                      rfl

theorem cell23_4979919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 7].length) (baseStart_4979919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4979919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4979919 prefixEnd_4979919 := by exact prefixLift 4979919
  have htrace : WordTrace (prefixWord ++ tailWord_4979919) baseStart_4979919 baseEnd_4979919 := by
    simpa [prefixWord, tailWord_4979919, baseEnd_4979919] using wordTrace_append hprefix tailTrace_4979919
  have hstable : (prefixWord ++ tailWord_4979919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4979919).length < 2 ^ (prefixWord ++ tailWord_4979919).sum := by decide
  have hdescent : baseEnd_4979919 < baseStart_4979919 := by decide
  rcases family_descends (prefixWord ++ tailWord_4979919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4979950 : List Nat := [4, 1, 2, 1, 1, 1, 3, 4, 2, 1, 3]
def baseStart_4979950 : Nat := 118140960795 + 4979950 * 2 ^ 59
def prefixEnd_4979950 : Nat := 4983230072969 + 3 ^ 40 * 4979950 * 2
def baseEnd_4979950 : Nat := 2557107985357896156422633

theorem tailTrace_4979950 : CollatzResearch.WordTrace tailWord_4979950 prefixEnd_4979950 2557107985357896156422633 := by
  unfold tailWord_4979950
  simp only [CollatzResearch.WordTrace]
  refine ⟨22704212288562391574091163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121089132205666088395152869 22704212288562391574091163)
  ·
    refine ⟨34056318432843587361136745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22704212288562391574091163 34056318432843587361136745)
    ·
      refine ⟨25542238824632690520852559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34056318432843587361136745 25542238824632690520852559)
      ·
        refine ⟨38313358236949035781278839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25542238824632690520852559 38313358236949035781278839)
        ·
          refine ⟨57470037355423553671918259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38313358236949035781278839 57470037355423553671918259)
          ·
            refine ⟨86205056033135330507877389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57470037355423553671918259 86205056033135330507877389)
            ·
              refine ⟨32326896012425748940454021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86205056033135330507877389 32326896012425748940454021)
              ·
                refine ⟨6061293002329827926335129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32326896012425748940454021 6061293002329827926335129)
                ·
                  refine ⟨4545969751747370944751347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6061293002329827926335129 4545969751747370944751347)
                  ·
                    refine ⟨6818954627621056417127021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4545969751747370944751347 6818954627621056417127021)
                    ·
                      refine ⟨2557107985357896156422633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6818954627621056417127021 2557107985357896156422633)
                      ·
                        rfl

theorem cell23_4979950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 4, 2, 1, 3].length) (baseStart_4979950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4979950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4979950 prefixEnd_4979950 := by exact prefixLift 4979950
  have htrace : WordTrace (prefixWord ++ tailWord_4979950) baseStart_4979950 baseEnd_4979950 := by
    simpa [prefixWord, tailWord_4979950, baseEnd_4979950] using wordTrace_append hprefix tailTrace_4979950
  have hstable : (prefixWord ++ tailWord_4979950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4979950).length < 2 ^ (prefixWord ++ tailWord_4979950).sum := by decide
  have hdescent : baseEnd_4979950 < baseStart_4979950 := by decide
  rcases family_descends (prefixWord ++ tailWord_4979950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4979951 : List Nat := [1, 1, 2, 1, 7, 2, 2, 2, 1, 2, 2]
def baseStart_4979951 : Nat := 118140960795 + 4979951 * 2 ^ 59
def prefixEnd_4979951 : Nat := 4983230072969 + 3 ^ 40 * 4979951 * 2
def baseEnd_4979951 : Nat := 2557108498838550652510129

theorem tailTrace_4979951 : CollatzResearch.WordTrace tailWord_4979951 prefixEnd_4979951 2557108498838550652510129 := by
  unfold tailWord_4979951
  simp only [CollatzResearch.WordTrace]
  refine ⟨181633734781495509763515707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121089156520997006509010471 181633734781495509763515707)
  ·
    refine ⟨272450602172243264645273561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181633734781495509763515707 272450602172243264645273561)
    ·
      refine ⟨204337951629182448483955171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 272450602172243264645273561 204337951629182448483955171)
      ·
        refine ⟨306506927443773672725932757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204337951629182448483955171 306506927443773672725932757)
        ·
          refine ⟨7183756111963445454514049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 306506927443773672725932757 7183756111963445454514049)
          ·
            refine ⟨5387817083972584090885537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7183756111963445454514049 5387817083972584090885537)
            ·
              refine ⟨4040862812979438068164153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5387817083972584090885537 4040862812979438068164153)
              ·
                refine ⟨3030647109734578551123115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4040862812979438068164153 3030647109734578551123115)
                ·
                  refine ⟨4545970664601867826684673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3030647109734578551123115 4545970664601867826684673)
                  ·
                    refine ⟨3409477998451400870013505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4545970664601867826684673 3409477998451400870013505)
                    ·
                      refine ⟨2557108498838550652510129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3409477998451400870013505 2557108498838550652510129)
                      ·
                        rfl

theorem cell23_4979951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 2, 1, 2, 2].length) (baseStart_4979951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4979951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4979951 prefixEnd_4979951 := by exact prefixLift 4979951
  have htrace : WordTrace (prefixWord ++ tailWord_4979951) baseStart_4979951 baseEnd_4979951 := by
    simpa [prefixWord, tailWord_4979951, baseEnd_4979951] using wordTrace_append hprefix tailTrace_4979951
  have hstable : (prefixWord ++ tailWord_4979951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4979951).length < 2 ^ (prefixWord ++ tailWord_4979951).sum := by decide
  have hdescent : baseEnd_4979951 < baseStart_4979951 := by decide
  rcases family_descends (prefixWord ++ tailWord_4979951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4979994 : List Nat := [3, 1, 1, 3, 3, 3, 2, 1, 1, 3, 2]
def baseStart_4979994 : Nat := 118140960795 + 4979994 * 2 ^ 59
def prefixEnd_4979994 : Nat := 4983230072969 + 3 ^ 40 * 4979994 * 2
def baseEnd_4979994 : Nat := 2557130578506693984272431

theorem tailTrace_4979994 : CollatzResearch.WordTrace tailWord_4979994 prefixEnd_4979994 2557130578506693984272431 := by
  unfold tailWord_4979994
  simp only [CollatzResearch.WordTrace]
  refine ⟨45408825780084932026832759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121090202080226485404887357 45408825780084932026832759)
  ·
    refine ⟨68113238670127398040249139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45408825780084932026832759 68113238670127398040249139)
    ·
      refine ⟨102169858005191097060373709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68113238670127398040249139 102169858005191097060373709)
      ·
        refine ⟨38313696751946661397640141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102169858005191097060373709 38313696751946661397640141)
        ·
          refine ⟨14367636281979998024115053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38313696751946661397640141 14367636281979998024115053)
          ·
            refine ⟨5387863605742499259043145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14367636281979998024115053 5387863605742499259043145)
            ·
              refine ⟨4040897704306874444282359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5387863605742499259043145 4040897704306874444282359)
              ·
                refine ⟨6061346556460311666423539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4040897704306874444282359 6061346556460311666423539)
                ·
                  refine ⟨9092019834690467499635309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6061346556460311666423539 9092019834690467499635309)
                  ·
                    refine ⟨3409507438008925312363241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9092019834690467499635309 3409507438008925312363241)
                    ·
                      refine ⟨2557130578506693984272431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3409507438008925312363241 2557130578506693984272431)
                      ·
                        rfl

theorem cell23_4979994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 1, 1, 3, 2].length) (baseStart_4979994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4979994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4979994 prefixEnd_4979994 := by exact prefixLift 4979994
  have htrace : WordTrace (prefixWord ++ tailWord_4979994) baseStart_4979994 baseEnd_4979994 := by
    simpa [prefixWord, tailWord_4979994, baseEnd_4979994] using wordTrace_append hprefix tailTrace_4979994
  have hstable : (prefixWord ++ tailWord_4979994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4979994).length < 2 ^ (prefixWord ++ tailWord_4979994).sum := by decide
  have hdescent : baseEnd_4979994 < baseStart_4979994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4979994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4980026 : List Nat := [3, 1, 1, 1, 4, 1, 1, 1, 3, 7]
def baseStart_4980026 : Nat := 118140960795 + 4980026 * 2 ^ 59
def prefixEnd_4980026 : Nat := 4983230072969 + 3 ^ 40 * 4980026 * 2
def baseEnd_4980026 : Nat := 852382336629212619690761

theorem tailTrace_4980026 : CollatzResearch.WordTrace tailWord_4980026 prefixEnd_4980026 852382336629212619690761 := by
  unfold tailWord_4980026
  simp only [CollatzResearch.WordTrace]
  refine ⟨45409117564055949393123983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121090980170815865048330621 45409117564055949393123983)
  ·
    refine ⟨68113676346083924089685975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45409117564055949393123983 68113676346083924089685975)
    ·
      refine ⟨102170514519125886134528963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68113676346083924089685975 102170514519125886134528963)
      ·
        refine ⟨153255771778688829201793445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102170514519125886134528963 153255771778688829201793445)
        ·
          refine ⟨28735457208504155475336271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 153255771778688829201793445 28735457208504155475336271)
          ·
            refine ⟨43103185812756233213004407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28735457208504155475336271 43103185812756233213004407)
            ·
              refine ⟨64654778719134349819506611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43103185812756233213004407 64654778719134349819506611)
              ·
                refine ⟨96982168078701524729259917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64654778719134349819506611 96982168078701524729259917)
                ·
                  refine ⟨36368313029513071773472469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96982168078701524729259917 36368313029513071773472469)
                  ·
                    refine ⟨852382336629212619690761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36368313029513071773472469 852382336629212619690761)
                    ·
                      rfl

theorem cell23_4980026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 3, 7].length) (baseStart_4980026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4980026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4980026 prefixEnd_4980026 := by exact prefixLift 4980026
  have htrace : WordTrace (prefixWord ++ tailWord_4980026) baseStart_4980026 baseEnd_4980026 := by
    simpa [prefixWord, tailWord_4980026, baseEnd_4980026] using wordTrace_append hprefix tailTrace_4980026
  have hstable : (prefixWord ++ tailWord_4980026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4980026).length < 2 ^ (prefixWord ++ tailWord_4980026).sum := by decide
  have hdescent : baseEnd_4980026 < baseStart_4980026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4980026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4980073 : List Nat := [1, 2, 1, 1, 1, 3, 2, 5, 3, 4]
def baseStart_4980073 : Nat := 118140960795 + 4980073 * 2 ^ 59
def prefixEnd_4980073 : Nat := 4983230072969 + 3 ^ 40 * 4980073 * 2
def baseEnd_4980073 : Nat := 852390381159466391728189

theorem tailTrace_4980073 : CollatzResearch.WordTrace tailWord_4980073 prefixEnd_4980073 852390381159466391728189 := by
  unfold tailWord_4980073
  simp only [CollatzResearch.WordTrace]
  refine ⟨181638184487053524599456873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121092122991369016399637915 181638184487053524599456873)
  ·
    refine ⟨136228638365290143449592655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181638184487053524599456873 136228638365290143449592655)
    ·
      refine ⟨204342957547935215174388983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136228638365290143449592655 204342957547935215174388983)
      ·
        refine ⟨306514436321902822761583475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204342957547935215174388983 306514436321902822761583475)
        ·
          refine ⟨459771654482854234142375213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 306514436321902822761583475 459771654482854234142375213)
          ·
            refine ⟨172414370431070337803390705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 459771654482854234142375213 172414370431070337803390705)
            ·
              refine ⟨129310777823302753352543029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 172414370431070337803390705 129310777823302753352543029)
              ·
                refine ⟨12122885420934633126800909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 129310777823302753352543029 12122885420934633126800909)
                ·
                  refine ⟨4546082032850487422550341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12122885420934633126800909 4546082032850487422550341)
                  ·
                    refine ⟨852390381159466391728189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4546082032850487422550341 852390381159466391728189)
                    ·
                      rfl

theorem cell23_4980073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5, 3, 4].length) (baseStart_4980073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4980073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4980073 prefixEnd_4980073 := by exact prefixLift 4980073
  have htrace : WordTrace (prefixWord ++ tailWord_4980073) baseStart_4980073 baseEnd_4980073 := by
    simpa [prefixWord, tailWord_4980073, baseEnd_4980073] using wordTrace_append hprefix tailTrace_4980073
  have hstable : (prefixWord ++ tailWord_4980073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4980073).length < 2 ^ (prefixWord ++ tailWord_4980073).sum := by decide
  have hdescent : baseEnd_4980073 < baseStart_4980073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4980073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4980094 : List Nat := [4, 2, 3, 2, 1, 1, 2, 1, 2, 5]
def baseStart_4980094 : Nat := 118140960795 + 4980094 * 2 ^ 59
def prefixEnd_4980094 : Nat := 4983230072969 + 3 ^ 40 * 4980094 * 2
def baseEnd_4980094 : Nat := 852393975524047864340657

theorem tailTrace_4980094 : CollatzResearch.WordTrace tailWord_4980094 prefixEnd_4980094 852393975524047864340657 := by
  unfold tailWord_4980094
  simp only [CollatzResearch.WordTrace]
  refine ⟨22704868802497180648246417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121092633613318296790647557 22704868802497180648246417)
  ·
    refine ⟨17028651601872885486184813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22704868802497180648246417 17028651601872885486184813)
    ·
      refine ⟨6385744350702332057319305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17028651601872885486184813 6385744350702332057319305)
      ·
        refine ⟨4789308263026749042989479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6385744350702332057319305 4789308263026749042989479)
        ·
          refine ⟨7183962394540123564484219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4789308263026749042989479 7183962394540123564484219)
          ·
            refine ⟨10775943591810185346726329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7183962394540123564484219 10775943591810185346726329)
            ·
              refine ⟨8081957693857639010044747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10775943591810185346726329 8081957693857639010044747)
              ·
                refine ⟨12122936540786458515067121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8081957693857639010044747 12122936540786458515067121)
                ·
                  refine ⟨9092202405589843886300341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12122936540786458515067121 9092202405589843886300341)
                  ·
                    refine ⟨852393975524047864340657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9092202405589843886300341 852393975524047864340657)
                    ·
                      rfl

theorem cell23_4980094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_4980094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4980094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4980094 prefixEnd_4980094 := by exact prefixLift 4980094
  have htrace : WordTrace (prefixWord ++ tailWord_4980094) baseStart_4980094 baseEnd_4980094 := by
    simpa [prefixWord, tailWord_4980094, baseEnd_4980094] using wordTrace_append hprefix tailTrace_4980094
  have hstable : (prefixWord ++ tailWord_4980094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4980094).length < 2 ^ (prefixWord ++ tailWord_4980094).sum := by decide
  have hdescent : baseEnd_4980094 < baseStart_4980094 := by decide
  rcases family_descends (prefixWord ++ tailWord_4980094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4980097 : List Nat := [1, 2, 4, 3, 2, 1, 2, 1, 2, 1, 4]
def baseStart_4980097 : Nat := 118140960795 + 4980097 * 2 ^ 59
def prefixEnd_4980097 : Nat := 4983230072969 + 3 ^ 40 * 4980097 * 2
def baseEnd_4980097 : Nat := 2557183467014107081284457

theorem tailTrace_4980097 : CollatzResearch.WordTrace tailWord_4980097 prefixEnd_4980097 2557183467014107081284457 := by
  unfold tailWord_4980097
  simp only [CollatzResearch.WordTrace]
  refine ⟨181639059838966576698330545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121092706559311051132220363 181639059838966576698330545)
  ·
    refine ⟨136229294879224932523747909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181639059838966576698330545 136229294879224932523747909)
    ·
      refine ⟨25542992789854674848202733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 136229294879224932523747909 25542992789854674848202733)
      ·
        refine ⟨9578622296195503068076025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25542992789854674848202733 9578622296195503068076025)
        ·
          refine ⟨7183966722146627301057019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9578622296195503068076025 7183966722146627301057019)
          ·
            refine ⟨10775950083219940951585529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7183966722146627301057019 10775950083219940951585529)
            ·
              refine ⟨8081962562414955713689147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10775950083219940951585529 8081962562414955713689147)
              ·
                refine ⟨12122943843622433570533721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8081962562414955713689147 12122943843622433570533721)
                ·
                  refine ⟨9092207882716825177900291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12122943843622433570533721 9092207882716825177900291)
                  ·
                    refine ⟨13638311824075237766850437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9092207882716825177900291 13638311824075237766850437)
                    ·
                      refine ⟨2557183467014107081284457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13638311824075237766850437 2557183467014107081284457)
                      ·
                        rfl

theorem cell23_4980097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_4980097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4980097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4980097 prefixEnd_4980097 := by exact prefixLift 4980097
  have htrace : WordTrace (prefixWord ++ tailWord_4980097) baseStart_4980097 baseEnd_4980097 := by
    simpa [prefixWord, tailWord_4980097, baseEnd_4980097] using wordTrace_append hprefix tailTrace_4980097
  have hstable : (prefixWord ++ tailWord_4980097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4980097).length < 2 ^ (prefixWord ++ tailWord_4980097).sum := by decide
  have hdescent : baseEnd_4980097 < baseStart_4980097 := by decide
  rcases family_descends (prefixWord ++ tailWord_4980097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4980100 : List Nat := [2, 3, 2, 1, 1, 3, 1, 3, 2, 2, 3]
def baseStart_4980100 : Nat := 118140960795 + 4980100 * 2 ^ 59
def prefixEnd_4980100 : Nat := 4983230072969 + 3 ^ 40 * 4980100 * 2
def baseEnd_4980100 : Nat := 2557185007456070569546943

theorem tailTrace_4980100 : CollatzResearch.WordTrace tailWord_4980100 prefixEnd_4980100 2557185007456070569546943 := by
  unfold tailWord_4980100
  simp only [CollatzResearch.WordTrace]
  refine ⟨90819584628977854105344877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121092779505303805473793169 90819584628977854105344877)
  ·
    refine ⟨34057344235866695289504329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90819584628977854105344877 34057344235866695289504329)
    ·
      refine ⟨25543008176900021467128247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34057344235866695289504329 25543008176900021467128247)
      ·
        refine ⟨38314512265350032200692371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25543008176900021467128247 38314512265350032200692371)
        ·
          refine ⟨57471768398025048301038557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38314512265350032200692371 57471768398025048301038557)
          ·
            refine ⟨21551913149259393112889459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57471768398025048301038557 21551913149259393112889459)
            ·
              refine ⟨32327869723889089669334189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21551913149259393112889459 32327869723889089669334189)
              ·
                refine ⟨12122951146458408626000321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32327869723889089669334189 12122951146458408626000321)
                ·
                  refine ⟨9092213359843806469500241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12122951146458408626000321 9092213359843806469500241)
                  ·
                    refine ⟨6819160019882854852125181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9092213359843806469500241 6819160019882854852125181)
                    ·
                      refine ⟨2557185007456070569546943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6819160019882854852125181 2557185007456070569546943)
                      ·
                        rfl

theorem cell23_4980100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_4980100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4980100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4980100 prefixEnd_4980100 := by exact prefixLift 4980100
  have htrace : WordTrace (prefixWord ++ tailWord_4980100) baseStart_4980100 baseEnd_4980100 := by
    simpa [prefixWord, tailWord_4980100, baseEnd_4980100] using wordTrace_append hprefix tailTrace_4980100
  have hstable : (prefixWord ++ tailWord_4980100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4980100).length < 2 ^ (prefixWord ++ tailWord_4980100).sum := by decide
  have hdescent : baseEnd_4980100 < baseStart_4980100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4980100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4980140 : List Nat := [2, 2, 1, 1, 1, 1, 4, 2, 4, 3, 2]
def baseStart_4980140 : Nat := 118140960795 + 4980140 * 2 ^ 59
def prefixEnd_4980140 : Nat := 4983230072969 + 3 ^ 40 * 4980140 * 2
def baseEnd_4980140 : Nat := 2557205546682250413046759

theorem tailTrace_4980140 : CollatzResearch.WordTrace tailWord_4980140 prefixEnd_4980140 2557205546682250413046759 := by
  unfold tailWord_4980140
  simp only [CollatzResearch.WordTrace]
  refine ⟨90820314088905397521072937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121093752118540530028097249 90820314088905397521072937)
  ·
    refine ⟨68115235566679048140804703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90820314088905397521072937 68115235566679048140804703)
    ·
      refine ⟨102172853350018572211207055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68115235566679048140804703 102172853350018572211207055)
      ·
        refine ⟨153259280025027858316810583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102172853350018572211207055 153259280025027858316810583)
        ·
          refine ⟨229888920037541787475215875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153259280025027858316810583 229888920037541787475215875)
          ·
            refine ⟨344833380056312681212823813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229888920037541787475215875 344833380056312681212823813)
            ·
              refine ⟨64656258760558627727404465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 344833380056312681212823813 64656258760558627727404465)
              ·
                refine ⟨48492194070418970795553349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64656258760558627727404465 48492194070418970795553349)
                ·
                  refine ⟨9092286388203557024166253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48492194070418970795553349 9092286388203557024166253)
                  ·
                    refine ⟨3409607395576333884062345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9092286388203557024166253 3409607395576333884062345)
                    ·
                      refine ⟨2557205546682250413046759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3409607395576333884062345 2557205546682250413046759)
                      ·
                        rfl

theorem cell23_4980140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 3, 2].length) (baseStart_4980140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4980140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4980140 prefixEnd_4980140 := by exact prefixLift 4980140
  have htrace : WordTrace (prefixWord ++ tailWord_4980140) baseStart_4980140 baseEnd_4980140 := by
    simpa [prefixWord, tailWord_4980140, baseEnd_4980140] using wordTrace_append hprefix tailTrace_4980140
  have hstable : (prefixWord ++ tailWord_4980140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4980140).length < 2 ^ (prefixWord ++ tailWord_4980140).sum := by decide
  have hdescent : baseEnd_4980140 < baseStart_4980140 := by decide
  rcases family_descends (prefixWord ++ tailWord_4980140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4980163 : List Nat := [1, 1, 1, 3, 1, 1, 6, 2, 1, 6]
def baseStart_4980163 : Nat := 118140960795 + 4980163 * 2 ^ 59
def prefixEnd_4980163 : Nat := 4983230072969 + 3 ^ 40 * 4980163 * 2
def baseEnd_4980163 : Nat := 852405785579101274353051

theorem tailTrace_4980163 : CollatzResearch.WordTrace tailWord_4980163 prefixEnd_4980163 852405785579101274353051 := by
  unfold tailWord_4980163
  simp only [CollatzResearch.WordTrace]
  refine ⟨181641467056727469970233143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121094311371151646646822095 181641467056727469970233143)
  ·
    refine ⟨272462200585091204955349715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181641467056727469970233143 272462200585091204955349715)
    ·
      refine ⟨408693300877636807433024573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272462200585091204955349715 408693300877636807433024573)
      ·
        refine ⟨153259987829113802787384215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 408693300877636807433024573 153259987829113802787384215)
        ·
          refine ⟨229889981743670704181076323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153259987829113802787384215 229889981743670704181076323)
          ·
            refine ⟨344834972615506056271614485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229889981743670704181076323 344834972615506056271614485)
            ·
              refine ⟨16164139341351846387731929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 344834972615506056271614485 16164139341351846387731929)
              ·
                refine ⟨12123104506013884790798947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16164139341351846387731929 12123104506013884790798947)
                ·
                  refine ⟨18184656759020827186198421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12123104506013884790798947 18184656759020827186198421)
                  ·
                    refine ⟨852405785579101274353051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18184656759020827186198421 852405785579101274353051)
                    ·
                      rfl

theorem cell23_4980163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2, 1, 6].length) (baseStart_4980163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4980163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4980163 prefixEnd_4980163 := by exact prefixLift 4980163
  have htrace : WordTrace (prefixWord ++ tailWord_4980163) baseStart_4980163 baseEnd_4980163 := by
    simpa [prefixWord, tailWord_4980163, baseEnd_4980163] using wordTrace_append hprefix tailTrace_4980163
  have hstable : (prefixWord ++ tailWord_4980163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4980163).length < 2 ^ (prefixWord ++ tailWord_4980163).sum := by decide
  have hdescent : baseEnd_4980163 < baseStart_4980163 := by decide
  rcases family_descends (prefixWord ++ tailWord_4980163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4980183 : List Nat := [1, 1, 3, 2, 1, 1, 1, 4, 3, 2, 4]
def baseStart_4980183 : Nat := 118140960795 + 4980183 * 2 ^ 59
def prefixEnd_4980183 : Nat := 4983230072969 + 3 ^ 40 * 4980183 * 2
def baseEnd_4980183 : Nat := 2557227626350393744809061

theorem tailTrace_4980183 : CollatzResearch.WordTrace tailWord_4980183 prefixEnd_4980183 2557227626350393744809061 := by
  unfold tailWord_4980183
  simp only [CollatzResearch.WordTrace]
  refine ⟨181642196516655013385961203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121094797677770008923974135 181642196516655013385961203)
  ·
    refine ⟨272463294774982520078941805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181642196516655013385961203 272463294774982520078941805)
    ·
      refine ⟨102173735540618445029603177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 272463294774982520078941805 102173735540618445029603177)
      ·
        refine ⟨76630301655463833772202383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102173735540618445029603177 76630301655463833772202383)
        ·
          refine ⟨114945452483195750658303575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76630301655463833772202383 114945452483195750658303575)
          ·
            refine ⟨172418178724793625987455363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114945452483195750658303575 172418178724793625987455363)
            ·
              refine ⟨258627268087190438981183045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172418178724793625987455363 258627268087190438981183045)
              ·
                refine ⟨48492612766348207308971821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 258627268087190438981183045 48492612766348207308971821)
                ·
                  refine ⟨18184729787380577740864433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48492612766348207308971821 18184729787380577740864433)
                  ·
                    refine ⟨13638547340535433305648325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18184729787380577740864433 13638547340535433305648325)
                    ·
                      refine ⟨2557227626350393744809061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13638547340535433305648325 2557227626350393744809061)
                      ·
                        rfl

theorem cell23_4980183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_4980183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4980183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4980183 prefixEnd_4980183 := by exact prefixLift 4980183
  have htrace : WordTrace (prefixWord ++ tailWord_4980183) baseStart_4980183 baseEnd_4980183 := by
    simpa [prefixWord, tailWord_4980183, baseEnd_4980183] using wordTrace_append hprefix tailTrace_4980183
  have hstable : (prefixWord ++ tailWord_4980183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4980183).length < 2 ^ (prefixWord ++ tailWord_4980183).sum := by decide
  have hdescent : baseEnd_4980183 < baseStart_4980183 := by decide
  rcases family_descends (prefixWord ++ tailWord_4980183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4980197 : List Nat := [1, 3, 1, 5, 1, 3, 1, 1, 1, 6]
def baseStart_4980197 : Nat := 118140960795 + 4980197 * 2 ^ 59
def prefixEnd_4980197 : Nat := 4983230072969 + 3 ^ 40 * 4980197 * 2
def baseEnd_4980197 : Nat := 852411605026518896677999

theorem tailTrace_4980197 : CollatzResearch.WordTrace tailWord_4980197 prefixEnd_4980197 852411605026518896677999 := by
  unfold tailWord_4980197
  simp only [CollatzResearch.WordTrace]
  refine ⟨181642707138604293776970845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121095138092402862517980563 181642707138604293776970845)
  ·
    refine ⟨68116015176976610166364067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181642707138604293776970845 68116015176976610166364067)
    ·
      refine ⟨102174022765464915249546101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68116015176976610166364067 102174022765464915249546101)
      ·
        refine ⟨9578814634262335804644947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 102174022765464915249546101 9578814634262335804644947)
        ·
          refine ⟨14368221951393503706967421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9578814634262335804644947 14368221951393503706967421)
          ·
            refine ⟨5388083231772563890112783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14368221951393503706967421 5388083231772563890112783)
            ·
              refine ⟨8082124847658845835169175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5388083231772563890112783 8082124847658845835169175)
              ·
                refine ⟨12123187271488268752753763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8082124847658845835169175 12123187271488268752753763)
                ·
                  refine ⟨18184780907232403129130645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12123187271488268752753763 18184780907232403129130645)
                  ·
                    refine ⟨852411605026518896677999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18184780907232403129130645 852411605026518896677999)
                    ·
                      rfl

theorem cell23_4980197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 1, 1, 6].length) (baseStart_4980197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4980197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4980197 prefixEnd_4980197 := by exact prefixLift 4980197
  have htrace : WordTrace (prefixWord ++ tailWord_4980197) baseStart_4980197 baseEnd_4980197 := by
    simpa [prefixWord, tailWord_4980197, baseEnd_4980197] using wordTrace_append hprefix tailTrace_4980197
  have hstable : (prefixWord ++ tailWord_4980197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4980197).length < 2 ^ (prefixWord ++ tailWord_4980197).sum := by decide
  have hdescent : baseEnd_4980197 < baseStart_4980197 := by decide
  rcases family_descends (prefixWord ++ tailWord_4980197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4980210 : List Nat := [3, 2, 1, 4, 1, 2, 1, 9]
def baseStart_4980210 : Nat := 118140960795 + 4980210 * 2 ^ 59
def prefixEnd_4980210 : Nat := 4983230072969 + 3 ^ 40 * 4980210 * 2
def baseEnd_4980210 : Nat := 94712647789928338487831

theorem tailTrace_4980210 : CollatzResearch.WordTrace tailWord_4980210 prefixEnd_4980210 94712647789928338487831 := by
  unfold tailWord_4980210
  simp only [CollatzResearch.WordTrace]
  refine ⟨45410795321889299249298521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121095454191704797998129389 45410795321889299249298521)
  ·
    refine ⟨34058096491416974436973891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45410795321889299249298521 34058096491416974436973891)
    ·
      refine ⟨51087144737125461655460837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34058096491416974436973891 51087144737125461655460837)
      ·
        refine ⟨9578839638211024060398907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51087144737125461655460837 9578839638211024060398907)
        ·
          refine ⟨14368259457316536090598361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9578839638211024060398907 14368259457316536090598361)
          ·
            refine ⟨10776194592987402067948771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14368259457316536090598361 10776194592987402067948771)
            ·
              refine ⟨16164291889481103101923157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10776194592987402067948771 16164291889481103101923157)
              ·
                refine ⟨94712647789928338487831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16164291889481103101923157 94712647789928338487831)
                ·
                  rfl

theorem cell23_4980210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 9].length) (baseStart_4980210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4980210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4980210 prefixEnd_4980210 := by exact prefixLift 4980210
  have htrace : WordTrace (prefixWord ++ tailWord_4980210) baseStart_4980210 baseEnd_4980210 := by
    simpa [prefixWord, tailWord_4980210, baseEnd_4980210] using wordTrace_append hprefix tailTrace_4980210
  have hstable : (prefixWord ++ tailWord_4980210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4980210).length < 2 ^ (prefixWord ++ tailWord_4980210).sum := by decide
  have hdescent : baseEnd_4980210 < baseStart_4980210 := by decide
  rcases family_descends (prefixWord ++ tailWord_4980210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4980220 : List Nat := [2, 2, 2, 1, 2, 1, 2, 4, 1, 3, 3]
def baseStart_4980220 : Nat := 118140960795 + 4980220 * 2 ^ 59
def prefixEnd_4980220 : Nat := 4983230072969 + 3 ^ 40 * 4980220 * 2
def baseEnd_4980220 : Nat := 2557246625134610100046391

theorem tailTrace_4980220 : CollatzResearch.WordTrace tailWord_4980220 prefixEnd_4980220 2557246625134610100046391 := by
  unfold tailWord_4980220
  simp only [CollatzResearch.WordTrace]
  refine ⟨90821773008760484352529057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121095697345013979136705409 90821773008760484352529057)
  ·
    refine ⟨68116329756570363264396793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90821773008760484352529057 68116329756570363264396793)
    ·
      refine ⟨51087247317427772448297595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68116329756570363264396793 51087247317427772448297595)
      ·
        refine ⟨76630870976141658672446393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51087247317427772448297595 76630870976141658672446393)
        ·
          refine ⟨57473153232106244004334795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76630870976141658672446393 57473153232106244004334795)
          ·
            refine ⟨86209729848159366006502193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57473153232106244004334795 86209729848159366006502193)
            ·
              refine ⟨64657297386119524504876645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86209729848159366006502193 64657297386119524504876645)
              ·
                refine ⟨12123243259897410844664371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64657297386119524504876645 12123243259897410844664371)
                ·
                  refine ⟨18184864889846116266996557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12123243259897410844664371 18184864889846116266996557)
                  ·
                    refine ⟨6819324333692293600123709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18184864889846116266996557 6819324333692293600123709)
                    ·
                      refine ⟨2557246625134610100046391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6819324333692293600123709 2557246625134610100046391)
                      ·
                        rfl

theorem cell23_4980220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4, 1, 3, 3].length) (baseStart_4980220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4980220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4980220 prefixEnd_4980220 := by exact prefixLift 4980220
  have htrace : WordTrace (prefixWord ++ tailWord_4980220) baseStart_4980220 baseEnd_4980220 := by
    simpa [prefixWord, tailWord_4980220, baseEnd_4980220] using wordTrace_append hprefix tailTrace_4980220
  have hstable : (prefixWord ++ tailWord_4980220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4980220).length < 2 ^ (prefixWord ++ tailWord_4980220).sum := by decide
  have hdescent : baseEnd_4980220 < baseStart_4980220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4980220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4980221 : List Nat := [1, 4, 1, 1, 1, 4, 3, 3, 1, 2, 2]
def baseStart_4980221 : Nat := 118140960795 + 4980221 * 2 ^ 59
def prefixEnd_4980221 : Nat := 4983230072969 + 3 ^ 40 * 4980221 * 2
def baseEnd_4980221 : Nat := 2557247138615264596133887

theorem tailTrace_4980221 : CollatzResearch.WordTrace tailWord_4980221 prefixEnd_4980221 2557247138615264596133887 := by
  unfold tailWord_4980221
  simp only [CollatzResearch.WordTrace]
  refine ⟨181643582490517345875844517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121095721660344897250563011 181643582490517345875844517)
  ·
    refine ⟨34058171716972002351720847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 181643582490517345875844517 34058171716972002351720847)
    ·
      refine ⟨51087257575458003527581271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34058171716972002351720847 51087257575458003527581271)
      ·
        refine ⟨76630886363187005291371907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51087257575458003527581271 76630886363187005291371907)
        ·
          refine ⟨114946329544780507937057861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76630886363187005291371907 114946329544780507937057861)
          ·
            refine ⟨21552436789646345238198349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 114946329544780507937057861 21552436789646345238198349)
            ·
              refine ⟨8082163796117379464324381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21552436789646345238198349 8082163796117379464324381)
              ·
                refine ⟨3030811423544017299121643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8082163796117379464324381 3030811423544017299121643)
                ·
                  refine ⟨4546217135316025948682465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3030811423544017299121643 4546217135316025948682465)
                  ·
                    refine ⟨3409662851487019461511849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4546217135316025948682465 3409662851487019461511849)
                    ·
                      refine ⟨2557247138615264596133887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3409662851487019461511849 2557247138615264596133887)
                      ·
                        rfl

theorem cell23_4980221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 3, 1, 2, 2].length) (baseStart_4980221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4980221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4980221 prefixEnd_4980221 := by exact prefixLift 4980221
  have htrace : WordTrace (prefixWord ++ tailWord_4980221) baseStart_4980221 baseEnd_4980221 := by
    simpa [prefixWord, tailWord_4980221, baseEnd_4980221] using wordTrace_append hprefix tailTrace_4980221
  have hstable : (prefixWord ++ tailWord_4980221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4980221).length < 2 ^ (prefixWord ++ tailWord_4980221).sum := by decide
  have hdescent : baseEnd_4980221 < baseStart_4980221 := by decide
  rcases family_descends (prefixWord ++ tailWord_4980221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4980233 : List Nat := [1, 2, 1, 1, 3, 1, 3, 2, 2, 2, 5]
def baseStart_4980233 : Nat := 118140960795 + 4980233 * 2 ^ 59
def prefixEnd_4980233 : Nat := 4983230072969 + 3 ^ 40 * 4980233 * 2
def baseEnd_4980233 : Nat := 2557253300383118549183831

theorem tailTrace_4980233 : CollatzResearch.WordTrace tailWord_4980233 prefixEnd_4980233 2557253300383118549183831 := by
  unfold tailWord_4980233
  simp only [CollatzResearch.WordTrace]
  refine ⟨181644020166473871925281353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121096013444315914616854235 181644020166473871925281353)
  ·
    refine ⟨136233015124855403943961015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181644020166473871925281353 136233015124855403943961015)
    ·
      refine ⟨204349522687283105915941523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136233015124855403943961015 204349522687283105915941523)
      ·
        refine ⟨306524284030924658873912285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204349522687283105915941523 306524284030924658873912285)
        ·
          refine ⟨114946606511596747077717107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 306524284030924658873912285 114946606511596747077717107)
          ·
            refine ⟨172419909767395120616575661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114946606511596747077717107 172419909767395120616575661)
            ·
              refine ⟨64657466162773170231215873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 172419909767395120616575661 64657466162773170231215873)
              ·
                refine ⟨48493099622079877673411905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64657466162773170231215873 48493099622079877673411905)
                ·
                  refine ⟨36369824716559908255058929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48493099622079877673411905 36369824716559908255058929)
                  ·
                    refine ⟨27277368537419931191294197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36369824716559908255058929 27277368537419931191294197)
                    ·
                      refine ⟨2557253300383118549183831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27277368537419931191294197 2557253300383118549183831)
                      ·
                        rfl

theorem cell23_4980233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 2, 5].length) (baseStart_4980233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4980233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4980233 prefixEnd_4980233 := by exact prefixLift 4980233
  have htrace : WordTrace (prefixWord ++ tailWord_4980233) baseStart_4980233 baseEnd_4980233 := by
    simpa [prefixWord, tailWord_4980233, baseEnd_4980233] using wordTrace_append hprefix tailTrace_4980233
  have hstable : (prefixWord ++ tailWord_4980233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4980233).length < 2 ^ (prefixWord ++ tailWord_4980233).sum := by decide
  have hdescent : baseEnd_4980233 < baseStart_4980233 := by decide
  rcases family_descends (prefixWord ++ tailWord_4980233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4980238 : List Nat := [4, 1, 1, 2, 5, 1, 1, 1, 3, 2, 2]
def baseStart_4980238 : Nat := 118140960795 + 4980238 * 2 ^ 59
def prefixEnd_4980238 : Nat := 4983230072969 + 3 ^ 40 * 4980238 * 2
def baseEnd_4980238 : Nat := 2557255867786391029621309

theorem tailTrace_4980238 : CollatzResearch.WordTrace tailWord_4980238 prefixEnd_4980238 2557255867786391029621309 := by
  unfold tailWord_4980238
  simp only [CollatzResearch.WordTrace]
  refine ⟨22705525316431969722401671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121096135020970505186142245 22705525316431969722401671)
  ·
    refine ⟨34058287974647954583602507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22705525316431969722401671 34058287974647954583602507)
    ·
      refine ⟨51087431961971931875403761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34058287974647954583602507 51087431961971931875403761)
      ·
        refine ⟨38315573971478948906552821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51087431961971931875403761 38315573971478948906552821)
        ·
          refine ⟨3592085059826151459989327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38315573971478948906552821 3592085059826151459989327)
          ·
            refine ⟨5388127589739227189983991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3592085059826151459989327 5388127589739227189983991)
            ·
              refine ⟨8082191384608840784975987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5388127589739227189983991 8082191384608840784975987)
              ·
                refine ⟨12123287076913261177463981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8082191384608840784975987 12123287076913261177463981)
                ·
                  refine ⟨4546232653842472941548993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12123287076913261177463981 4546232653842472941548993)
                  ·
                    refine ⟨3409674490381854706161745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4546232653842472941548993 3409674490381854706161745)
                    ·
                      refine ⟨2557255867786391029621309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3409674490381854706161745 2557255867786391029621309)
                      ·
                        rfl

theorem cell23_4980238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 1, 3, 2, 2].length) (baseStart_4980238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4980238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4980238 prefixEnd_4980238 := by exact prefixLift 4980238
  have htrace : WordTrace (prefixWord ++ tailWord_4980238) baseStart_4980238 baseEnd_4980238 := by
    simpa [prefixWord, tailWord_4980238, baseEnd_4980238] using wordTrace_append hprefix tailTrace_4980238
  have hstable : (prefixWord ++ tailWord_4980238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4980238).length < 2 ^ (prefixWord ++ tailWord_4980238).sum := by decide
  have hdescent : baseEnd_4980238 < baseStart_4980238 := by decide
  rcases family_descends (prefixWord ++ tailWord_4980238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4980277 : List Nat := [1, 3, 3, 1, 1, 3, 1, 1, 3, 4, 2]
def baseStart_4980277 : Nat := 118140960795 + 4980277 * 2 ^ 59
def prefixEnd_4980277 : Nat := 4983230072969 + 3 ^ 40 * 4980277 * 2
def baseEnd_4980277 : Nat := 2557275893531916377033629

theorem tailTrace_4980277 : CollatzResearch.WordTrace tailWord_4980277 prefixEnd_4980277 2557275893531916377033629 := by
  unfold tailWord_4980277
  simp only [CollatzResearch.WordTrace]
  refine ⟨181645624978314467439883085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121097083318876311626588723 181645624978314467439883085)
  ·
    refine ⟨68117109366867925289956157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181645624978314467439883085 68117109366867925289956157)
    ·
      refine ⟨25543916012575471983733559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68117109366867925289956157 25543916012575471983733559)
      ·
        refine ⟨38315874018863207975600339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25543916012575471983733559 38315874018863207975600339)
        ·
          refine ⟨57473811028294811963400509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38315874018863207975600339 57473811028294811963400509)
          ·
            refine ⟨21552679135610554486275191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57473811028294811963400509 21552679135610554486275191)
            ·
              refine ⟨32329018703415831729412787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21552679135610554486275191 32329018703415831729412787)
              ·
                refine ⟨48493528055123747594119181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32329018703415831729412787 48493528055123747594119181)
                ·
                  refine ⟨18185073020671405347794693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48493528055123747594119181 18185073020671405347794693)
                  ·
                    refine ⟨3409701191375888502711505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18185073020671405347794693 3409701191375888502711505)
                    ·
                      refine ⟨2557275893531916377033629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3409701191375888502711505 2557275893531916377033629)
                      ·
                        rfl

theorem cell23_4980277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3, 4, 2].length) (baseStart_4980277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4980277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4980277 prefixEnd_4980277 := by exact prefixLift 4980277
  have htrace : WordTrace (prefixWord ++ tailWord_4980277) baseStart_4980277 baseEnd_4980277 := by
    simpa [prefixWord, tailWord_4980277, baseEnd_4980277] using wordTrace_append hprefix tailTrace_4980277
  have hstable : (prefixWord ++ tailWord_4980277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4980277).length < 2 ^ (prefixWord ++ tailWord_4980277).sum := by decide
  have hdescent : baseEnd_4980277 < baseStart_4980277 := by decide
  rcases family_descends (prefixWord ++ tailWord_4980277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4980280 : List Nat := [2, 1, 2, 1, 4, 2, 2, 1, 2, 1, 5]
def baseStart_4980280 : Nat := 118140960795 + 4980280 * 2 ^ 59
def prefixEnd_4980280 : Nat := 4983230072969 + 3 ^ 40 * 4980280 * 2
def baseEnd_4980280 : Nat := 2557277433973879865296115

theorem tailTrace_4980280 : CollatzResearch.WordTrace tailWord_4980280 prefixEnd_4980280 2557277433973879865296115 := by
  unfold tailWord_4980280
  simp only [CollatzResearch.WordTrace]
  refine ⟨90822867198651799476121147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121097156264869065968161529 90822867198651799476121147)
  ·
    refine ⟨136234300797977699214181721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90822867198651799476121147 136234300797977699214181721)
    ·
      refine ⟨102175725598483274410636291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136234300797977699214181721 102175725598483274410636291)
      ·
        refine ⟨153263588397724911615954437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102175725598483274410636291 153263588397724911615954437)
        ·
          refine ⟨28736922824573420927991457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 153263588397724911615954437 28736922824573420927991457)
          ·
            refine ⟨21552692118430065695993593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28736922824573420927991457 21552692118430065695993593)
            ·
              refine ⟨16164519088822549271995195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21552692118430065695993593 16164519088822549271995195)
              ·
                refine ⟨24246778633233823907992793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16164519088822549271995195 24246778633233823907992793)
                ·
                  refine ⟨18185083974925367930994595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24246778633233823907992793 18185083974925367930994595)
                  ·
                    refine ⟨27277625962388051896491893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18185083974925367930994595 27277625962388051896491893)
                    ·
                      refine ⟨2557277433973879865296115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27277625962388051896491893 2557277433973879865296115)
                      ·
                        rfl

theorem cell23_4980280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 2, 1, 5].length) (baseStart_4980280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4980280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4980280 prefixEnd_4980280 := by exact prefixLift 4980280
  have htrace : WordTrace (prefixWord ++ tailWord_4980280) baseStart_4980280 baseEnd_4980280 := by
    simpa [prefixWord, tailWord_4980280, baseEnd_4980280] using wordTrace_append hprefix tailTrace_4980280
  have hstable : (prefixWord ++ tailWord_4980280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4980280).length < 2 ^ (prefixWord ++ tailWord_4980280).sum := by decide
  have hdescent : baseEnd_4980280 < baseStart_4980280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4980280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4980281 : List Nat := [1, 2, 1, 5, 1, 3, 3, 1, 1, 3, 2]
def baseStart_4980281 : Nat := 118140960795 + 4980281 * 2 ^ 59
def prefixEnd_4980281 : Nat := 4983230072969 + 3 ^ 40 * 4980281 * 2
def baseEnd_4980281 : Nat := 2557277947454534361383611

theorem tailTrace_4980281 : CollatzResearch.WordTrace tailWord_4980281 prefixEnd_4980281 2557277947454534361383611 := by
  unfold tailWord_4980281
  simp only [CollatzResearch.WordTrace]
  refine ⟨181645770870299976123028697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121097180580199984082019131 181645770870299976123028697)
  ·
    refine ⟨136234328152724982092271523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181645770870299976123028697 136234328152724982092271523)
    ·
      refine ⟨204351492229087473138407285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136234328152724982092271523 204351492229087473138407285)
      ·
        refine ⟨19157952396476950606725683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 204351492229087473138407285 19157952396476950606725683)
        ·
          refine ⟨28736928594715425910088525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19157952396476950606725683 28736928594715425910088525)
          ·
            refine ⟨10776348223018284716283197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28736928594715425910088525 10776348223018284716283197)
            ·
              refine ⟨4041130583631856768606199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10776348223018284716283197 4041130583631856768606199)
              ·
                refine ⟨6061695875447785152909299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4041130583631856768606199 6061695875447785152909299)
                ·
                  refine ⟨9092543813171677729363949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6061695875447785152909299 9092543813171677729363949)
                  ·
                    refine ⟨3409703929939379148511481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9092543813171677729363949 3409703929939379148511481)
                    ·
                      refine ⟨2557277947454534361383611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3409703929939379148511481 2557277947454534361383611)
                      ·
                        rfl

theorem cell23_4980281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_4980281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4980281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4980281 prefixEnd_4980281 := by exact prefixLift 4980281
  have htrace : WordTrace (prefixWord ++ tailWord_4980281) baseStart_4980281 baseEnd_4980281 := by
    simpa [prefixWord, tailWord_4980281, baseEnd_4980281] using wordTrace_append hprefix tailTrace_4980281
  have hstable : (prefixWord ++ tailWord_4980281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4980281).length < 2 ^ (prefixWord ++ tailWord_4980281).sum := by decide
  have hdescent : baseEnd_4980281 < baseStart_4980281 := by decide
  rcases family_descends (prefixWord ++ tailWord_4980281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4980303 : List Nat := [1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 8]
def baseStart_4980303 : Nat := 118140960795 + 4980303 * 2 ^ 59
def prefixEnd_4980303 : Nat := 4983230072969 + 3 ^ 40 * 4980303 * 2
def baseEnd_4980303 : Nat := 2557289244028933275308509

theorem tailTrace_4980303 : CollatzResearch.WordTrace tailWord_4980303 prefixEnd_4980303 2557289244028933275308509 := by
  unfold tailWord_4980303
  simp only [CollatzResearch.WordTrace]
  refine ⟨181646573276220273880329563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121097715517480182586886375 181646573276220273880329563)
  ·
    refine ⟨272469859914330410820494345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181646573276220273880329563 272469859914330410820494345)
    ·
      refine ⟨204352394935747808115370759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 272469859914330410820494345 204352394935747808115370759)
      ·
        refine ⟨306528592403621712173056139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204352394935747808115370759 306528592403621712173056139)
        ·
          refine ⟨459792888605432568259584209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 306528592403621712173056139 459792888605432568259584209)
          ·
            refine ⟨344844666454074426194688157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 459792888605432568259584209 344844666454074426194688157)
            ·
              refine ⟨129316749920277909823008059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 344844666454074426194688157 129316749920277909823008059)
              ·
                refine ⟨193975124880416864734512089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129316749920277909823008059 193975124880416864734512089)
                ·
                  refine ⟨145481343660312648550884067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 193975124880416864734512089 145481343660312648550884067)
                  ·
                    refine ⟨218222015490468972826326101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 145481343660312648550884067 218222015490468972826326101)
                    ·
                      refine ⟨2557289244028933275308509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 218222015490468972826326101 2557289244028933275308509)
                      ·
                        rfl

theorem cell23_4980303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 8].length) (baseStart_4980303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4980303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4980303 prefixEnd_4980303 := by exact prefixLift 4980303
  have htrace : WordTrace (prefixWord ++ tailWord_4980303) baseStart_4980303 baseEnd_4980303 := by
    simpa [prefixWord, tailWord_4980303, baseEnd_4980303] using wordTrace_append hprefix tailTrace_4980303
  have hstable : (prefixWord ++ tailWord_4980303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4980303).length < 2 ^ (prefixWord ++ tailWord_4980303).sum := by decide
  have hdescent : baseEnd_4980303 < baseStart_4980303 := by decide
  rcases family_descends (prefixWord ++ tailWord_4980303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4980387 : List Nat := [1, 1, 1, 4, 1, 1, 4, 3, 2, 2, 3]
def baseStart_4980387 : Nat := 118140960795 + 4980387 * 2 ^ 59
def prefixEnd_4980387 : Nat := 4983230072969 + 3 ^ 40 * 4980387 * 2
def baseEnd_4980387 : Nat := 2557332376403910946658123

theorem tailTrace_4980387 : CollatzResearch.WordTrace tailWord_4980387 prefixEnd_4980387 2557332376403910946658123 := by
  unfold tailWord_4980387
  simp only [CollatzResearch.WordTrace]
  refine ⟨181649637007915956226387415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121099758005277304150924943 181649637007915956226387415)
  ·
    refine ⟨272474455511873934339581123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181649637007915956226387415 272474455511873934339581123)
    ·
      refine ⟨408711683267810901509371685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272474455511873934339581123 408711683267810901509371685)
      ·
        refine ⟨76633440612714544033007191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 408711683267810901509371685 76633440612714544033007191)
        ·
          refine ⟨114950160919071816049510787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76633440612714544033007191 114950160919071816049510787)
          ·
            refine ⟨172425241378607724074266181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114950160919071816049510787 172425241378607724074266181)
            ·
              refine ⟨32329732758488948263924909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 172425241378607724074266181 32329732758488948263924909)
              ·
                refine ⟨12123649784433355598971841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32329732758488948263924909 12123649784433355598971841)
                ·
                  refine ⟨9092737338325016699228881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12123649784433355598971841 9092737338325016699228881)
                  ·
                    refine ⟨6819553003743762524421661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9092737338325016699228881 6819553003743762524421661)
                    ·
                      refine ⟨2557332376403910946658123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6819553003743762524421661 2557332376403910946658123)
                      ·
                        rfl

theorem cell23_4980387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3, 2, 2, 3].length) (baseStart_4980387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4980387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4980387 prefixEnd_4980387 := by exact prefixLift 4980387
  have htrace : WordTrace (prefixWord ++ tailWord_4980387) baseStart_4980387 baseEnd_4980387 := by
    simpa [prefixWord, tailWord_4980387, baseEnd_4980387] using wordTrace_append hprefix tailTrace_4980387
  have hstable : (prefixWord ++ tailWord_4980387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4980387).length < 2 ^ (prefixWord ++ tailWord_4980387).sum := by decide
  have hdescent : baseEnd_4980387 < baseStart_4980387 := by decide
  rcases family_descends (prefixWord ++ tailWord_4980387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4980427 : List Nat := [1, 1, 1, 1, 3, 2, 1, 3, 3, 5, 2]
def baseStart_4980427 : Nat := 118140960795 + 4980427 * 2 ^ 59
def prefixEnd_4980427 : Nat := 4983230072969 + 3 ^ 40 * 4980427 * 2
def baseEnd_4980427 : Nat := 2557352915630090790157939

theorem tailTrace_4980427 : CollatzResearch.WordTrace tailWord_4980427 prefixEnd_4980427 2557352915630090790157939 := by
  unfold tailWord_4980427
  simp only [CollatzResearch.WordTrace]
  refine ⟨181651095927771043057843535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121100730618514028705229023 181651095927771043057843535)
  ·
    refine ⟨272476643891656564586765303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181651095927771043057843535 272476643891656564586765303)
    ·
      refine ⟨408714965837484846880147955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272476643891656564586765303 408714965837484846880147955)
      ·
        refine ⟨613072448756227270320221933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 408714965837484846880147955 613072448756227270320221933)
        ·
          refine ⟨229902168283585226370083225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 613072448756227270320221933 229902168283585226370083225)
          ·
            refine ⟨172426626212688919777562419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 229902168283585226370083225 172426626212688919777562419)
            ·
              refine ⟨258639939319033379666343629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172426626212688919777562419 258639939319033379666343629)
              ·
                refine ⟨96989977244637517374878861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 258639939319033379666343629 96989977244637517374878861)
                ·
                  refine ⟨36371241466739069015579573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96989977244637517374878861 36371241466739069015579573)
                  ·
                    refine ⟨3409803887506787720210585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36371241466739069015579573 3409803887506787720210585)
                    ·
                      refine ⟨2557352915630090790157939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3409803887506787720210585 2557352915630090790157939)
                      ·
                        rfl

theorem cell23_4980427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 5, 2].length) (baseStart_4980427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4980427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4980427 prefixEnd_4980427 := by exact prefixLift 4980427
  have htrace : WordTrace (prefixWord ++ tailWord_4980427) baseStart_4980427 baseEnd_4980427 := by
    simpa [prefixWord, tailWord_4980427, baseEnd_4980427] using wordTrace_append hprefix tailTrace_4980427
  have hstable : (prefixWord ++ tailWord_4980427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4980427).length < 2 ^ (prefixWord ++ tailWord_4980427).sum := by decide
  have hdescent : baseEnd_4980427 < baseStart_4980427 := by decide
  rcases family_descends (prefixWord ++ tailWord_4980427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4980461 : List Nat := [1, 5, 1, 2, 1, 2, 2, 2, 2, 3, 2]
def baseStart_4980461 : Nat := 118140960795 + 4980461 * 2 ^ 59
def prefixEnd_4980461 : Nat := 4983230072969 + 3 ^ 40 * 4980461 * 2
def baseEnd_4980461 : Nat := 2557370373972343657132783

theorem tailTrace_4980461 : CollatzResearch.WordTrace tailWord_4980461 prefixEnd_4980461 2557370373972343657132783 := by
  unfold tailWord_4980461
  simp only [CollatzResearch.WordTrace]
  refine ⟨181652336009647866864581237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121101557339765244576387491 181652336009647866864581237)
  ·
    refine ⟨17029906500904487518554491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 181652336009647866864581237 17029906500904487518554491)
    ·
      refine ⟨25544859751356731277831737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17029906500904487518554491 25544859751356731277831737)
      ·
        refine ⟨19158644813517548458373803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25544859751356731277831737 19158644813517548458373803)
        ·
          refine ⟨28737967220276322687560705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19158644813517548458373803 28737967220276322687560705)
          ·
            refine ⟨21553475415207242015670529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28737967220276322687560705 21553475415207242015670529)
            ·
              refine ⟨16165106561405431511752897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21553475415207242015670529 16165106561405431511752897)
              ·
                refine ⟨12123829921054073633814673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16165106561405431511752897 12123829921054073633814673)
                ·
                  refine ⟨9092872440790555225361005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12123829921054073633814673 9092872440790555225361005)
                  ·
                    refine ⟨3409827165296458209510377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9092872440790555225361005 3409827165296458209510377)
                    ·
                      refine ⟨2557370373972343657132783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3409827165296458209510377 2557370373972343657132783)
                      ·
                        rfl

theorem cell23_4980461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_4980461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4980461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4980461 prefixEnd_4980461 := by exact prefixLift 4980461
  have htrace : WordTrace (prefixWord ++ tailWord_4980461) baseStart_4980461 baseEnd_4980461 := by
    simpa [prefixWord, tailWord_4980461, baseEnd_4980461] using wordTrace_append hprefix tailTrace_4980461
  have hstable : (prefixWord ++ tailWord_4980461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4980461).length < 2 ^ (prefixWord ++ tailWord_4980461).sum := by decide
  have hdescent : baseEnd_4980461 < baseStart_4980461 := by decide
  rcases family_descends (prefixWord ++ tailWord_4980461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4980467 : List Nat := [1, 1, 1, 2, 2, 3, 2, 3, 4, 4]
def baseStart_4980467 : Nat := 118140960795 + 4980467 * 2 ^ 59
def prefixEnd_4980467 : Nat := 4983230072969 + 3 ^ 40 * 4980467 * 2
def baseEnd_4980467 : Nat := 852457818285423544552585

theorem tailTrace_4980467 : CollatzResearch.WordTrace tailWord_4980467 prefixEnd_4980467 852457818285423544552585 := by
  unfold tailWord_4980467
  simp only [CollatzResearch.WordTrace]
  refine ⟨181652554847626129889299655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121101703231750753259533103 181652554847626129889299655)
  ·
    refine ⟨272478832271439194833949483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181652554847626129889299655 272478832271439194833949483)
    ·
      refine ⟨408718248407158792250924225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272478832271439194833949483 408718248407158792250924225)
      ·
        refine ⟨306538686305369094188193169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 408718248407158792250924225 306538686305369094188193169)
        ·
          refine ⟨229904014729026820641144877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 306538686305369094188193169 229904014729026820641144877)
          ·
            refine ⟨86214005523385057740429329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 229904014729026820641144877 86214005523385057740429329)
            ·
              refine ⟨64660504142538793305321997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86214005523385057740429329 64660504142538793305321997)
              ·
                refine ⟨24247689053452047489495749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64660504142538793305321997 24247689053452047489495749)
                ·
                  refine ⟨4546441697522258904280453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24247689053452047489495749 4546441697522258904280453)
                  ·
                    refine ⟨852457818285423544552585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4546441697522258904280453 852457818285423544552585)
                    ·
                      rfl

theorem cell23_4980467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 4, 4].length) (baseStart_4980467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4980467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4980467 prefixEnd_4980467 := by exact prefixLift 4980467
  have htrace : WordTrace (prefixWord ++ tailWord_4980467) baseStart_4980467 baseEnd_4980467 := by
    simpa [prefixWord, tailWord_4980467, baseEnd_4980467] using wordTrace_append hprefix tailTrace_4980467
  have hstable : (prefixWord ++ tailWord_4980467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4980467).length < 2 ^ (prefixWord ++ tailWord_4980467).sum := by decide
  have hdescent : baseEnd_4980467 < baseStart_4980467 := by decide
  rcases family_descends (prefixWord ++ tailWord_4980467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4980484 : List Nat := [2, 3, 2, 2, 1, 3, 2, 1, 1, 6]
def baseStart_4980484 : Nat := 118140960795 + 4980484 * 2 ^ 59
def prefixEnd_4980484 : Nat := 4983230072969 + 3 ^ 40 * 4980484 * 2
def baseEnd_4980484 : Nat := 852460728009132355715059

theorem tailTrace_4980484 : CollatzResearch.WordTrace tailWord_4980484 prefixEnd_4980484 852460728009132355715059 := by
  unfold tailWord_4980484
  simp only [CollatzResearch.WordTrace]
  refine ⟨90826587444282270896334253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121102116592376361195112337 90826587444282270896334253)
  ·
    refine ⟨34059970291605851586125345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90826587444282270896334253 34059970291605851586125345)
    ·
      refine ⟨25544977718704388689594009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34059970291605851586125345 25544977718704388689594009)
      ·
        refine ⟨19158733289028291517195507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25544977718704388689594009 19158733289028291517195507)
        ·
          refine ⟨28738099933542437275793261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19158733289028291517195507 28738099933542437275793261)
          ·
            refine ⟨10776787475078413978422473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28738099933542437275793261 10776787475078413978422473)
            ·
              refine ⟨8082590606308810483816855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10776787475078413978422473 8082590606308810483816855)
              ·
                refine ⟨12123885909463215725725283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8082590606308810483816855 12123885909463215725725283)
                ·
                  refine ⟨18185828864194823588587925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12123885909463215725725283 18185828864194823588587925)
                  ·
                    refine ⟨852460728009132355715059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18185828864194823588587925 852460728009132355715059)
                    ·
                      rfl

theorem cell23_4980484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_4980484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4980484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4980484 prefixEnd_4980484 := by exact prefixLift 4980484
  have htrace : WordTrace (prefixWord ++ tailWord_4980484) baseStart_4980484 baseEnd_4980484 := by
    simpa [prefixWord, tailWord_4980484, baseEnd_4980484] using wordTrace_append hprefix tailTrace_4980484
  have hstable : (prefixWord ++ tailWord_4980484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4980484).length < 2 ^ (prefixWord ++ tailWord_4980484).sum := by decide
  have hdescent : baseEnd_4980484 < baseStart_4980484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4980484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4980494 : List Nat := [4, 1, 1, 2, 1, 1, 4, 1, 3, 2, 3]
def baseStart_4980494 : Nat := 118140960795 + 4980494 * 2 ^ 59
def prefixEnd_4980494 : Nat := 4983230072969 + 3 ^ 40 * 4980494 * 2
def baseEnd_4980494 : Nat := 2557387318833942028020131

theorem tailTrace_4980494 : CollatzResearch.WordTrace tailWord_4980494 prefixEnd_4980494 2557387318833942028020131 := by
  unfold tailWord_4980494
  simp only [CollatzResearch.WordTrace]
  refine ⟨22706692452316039187566567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121102359745685542333688357 22706692452316039187566567)
  ·
    refine ⟨34060038678474058781349851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22706692452316039187566567 34060038678474058781349851)
    ·
      refine ⟨51090058017711088172024777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34060038678474058781349851 51090058017711088172024777)
      ·
        refine ⟨38317543513283316129018583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51090058017711088172024777 38317543513283316129018583)
        ·
          refine ⟨57476315269924974193527875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38317543513283316129018583 57476315269924974193527875)
          ·
            refine ⟨86214472904887461290291813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57476315269924974193527875 86214472904887461290291813)
            ·
              refine ⟨16165213669666398991929715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86214472904887461290291813 16165213669666398991929715)
              ·
                refine ⟨24247820504499598487894573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16165213669666398991929715 24247820504499598487894573)
                ·
                  refine ⟨9092932689187349432960465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24247820504499598487894573 9092932689187349432960465)
                  ·
                    refine ⟨6819699516890512074720349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9092932689187349432960465 6819699516890512074720349)
                    ·
                      refine ⟨2557387318833942028020131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6819699516890512074720349 2557387318833942028020131)
                      ·
                        rfl

theorem cell23_4980494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_4980494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4980494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4980494 prefixEnd_4980494 := by exact prefixLift 4980494
  have htrace : WordTrace (prefixWord ++ tailWord_4980494) baseStart_4980494 baseEnd_4980494 := by
    simpa [prefixWord, tailWord_4980494, baseEnd_4980494] using wordTrace_append hprefix tailTrace_4980494
  have hstable : (prefixWord ++ tailWord_4980494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4980494).length < 2 ^ (prefixWord ++ tailWord_4980494).sum := by decide
  have hdescent : baseEnd_4980494 < baseStart_4980494 := by decide
  rcases family_descends (prefixWord ++ tailWord_4980494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4980541 : List Nat := [1, 4, 1, 4, 1, 1, 3, 1, 1, 3, 3]
def baseStart_4980541 : Nat := 118140960795 + 4980541 * 2 ^ 59
def prefixEnd_4980541 : Nat := 4983230072969 + 3 ^ 40 * 4980541 * 2
def baseEnd_4980541 : Nat := 2557411452424703344132415

theorem tailTrace_4980541 : CollatzResearch.WordTrace tailWord_4980541 prefixEnd_4980541 2557411452424703344132415 := by
  unfold tailWord_4980541
  simp only [CollatzResearch.WordTrace]
  refine ⟨181655253849358040527493477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121103502566238693684995651 181655253849358040527493477)
  ·
    refine ⟨34060360096754632598905027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 181655253849358040527493477 34060360096754632598905027)
    ·
      refine ⟨51090540145131948898357541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34060360096754632598905027 51090540145131948898357541)
      ·
        refine ⟨9579476277212240418442039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51090540145131948898357541 9579476277212240418442039)
        ·
          refine ⟨14369214415818360627663059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9579476277212240418442039 14369214415818360627663059)
          ·
            refine ⟨21553821623727540941494589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14369214415818360627663059 21553821623727540941494589)
            ·
              refine ⟨8082683108897827853060471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21553821623727540941494589 8082683108897827853060471)
              ·
                refine ⟨12124024663346741779590707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8082683108897827853060471 12124024663346741779590707)
                ·
                  refine ⟨18186036995020112669386061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12124024663346741779590707 18186036995020112669386061)
                  ·
                    refine ⟨6819763873132542251019773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18186036995020112669386061 6819763873132542251019773)
                    ·
                      refine ⟨2557411452424703344132415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6819763873132542251019773 2557411452424703344132415)
                      ·
                        rfl

theorem cell23_4980541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_4980541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4980541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4980541 prefixEnd_4980541 := by exact prefixLift 4980541
  have htrace : WordTrace (prefixWord ++ tailWord_4980541) baseStart_4980541 baseEnd_4980541 := by
    simpa [prefixWord, tailWord_4980541, baseEnd_4980541] using wordTrace_append hprefix tailTrace_4980541
  have hstable : (prefixWord ++ tailWord_4980541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4980541).length < 2 ^ (prefixWord ++ tailWord_4980541).sum := by decide
  have hdescent : baseEnd_4980541 < baseStart_4980541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4980541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4980551 : List Nat := [1, 1, 4, 1, 2, 1, 3, 4, 1, 3, 2]
def baseStart_4980551 : Nat := 118140960795 + 4980551 * 2 ^ 59
def prefixEnd_4980551 : Nat := 4983230072969 + 3 ^ 40 * 4980551 * 2
def baseEnd_4980551 : Nat := 2557416587231248305007369

theorem tailTrace_4980551 : CollatzResearch.WordTrace tailWord_4980551 prefixEnd_4980551 2557416587231248305007369 := by
  unfold tailWord_4980551
  simp only [CollatzResearch.WordTrace]
  refine ⟨181655618579321812235357507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121103745719547874823571671 181655618579321812235357507)
  ·
    refine ⟨272483427868982718353036261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181655618579321812235357507 272483427868982718353036261)
    ·
      refine ⟨51090642725434259691194299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 272483427868982718353036261 51090642725434259691194299)
      ·
        refine ⟨76635964088151389536791449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51090642725434259691194299 76635964088151389536791449)
        ·
          refine ⟨57476973066113542152593587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76635964088151389536791449 57476973066113542152593587)
          ·
            refine ⟨86215459599170313228890381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57476973066113542152593587 86215459599170313228890381)
            ·
              refine ⟨32330797349688867460833893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86215459599170313228890381 32330797349688867460833893)
              ·
                refine ⟨6062024503066662648906355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32330797349688867460833893 6062024503066662648906355)
                ·
                  refine ⟨9093036754599993973359533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6062024503066662648906355 9093036754599993973359533)
                  ·
                    refine ⟨3409888782974997740009825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9093036754599993973359533 3409888782974997740009825)
                    ·
                      refine ⟨2557416587231248305007369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3409888782974997740009825 2557416587231248305007369)
                      ·
                        rfl

theorem cell23_4980551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 4, 1, 3, 2].length) (baseStart_4980551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4980551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4980551 prefixEnd_4980551 := by exact prefixLift 4980551
  have htrace : WordTrace (prefixWord ++ tailWord_4980551) baseStart_4980551 baseEnd_4980551 := by
    simpa [prefixWord, tailWord_4980551, baseEnd_4980551] using wordTrace_append hprefix tailTrace_4980551
  have hstable : (prefixWord ++ tailWord_4980551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4980551).length < 2 ^ (prefixWord ++ tailWord_4980551).sum := by decide
  have hdescent : baseEnd_4980551 < baseStart_4980551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4980551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4980584 : List Nat := [2, 1, 4, 2, 1, 1, 2, 1, 2, 4, 3]
def baseStart_4980584 : Nat := 118140960795 + 4980584 * 2 ^ 59
def prefixEnd_4980584 : Nat := 4983230072969 + 3 ^ 40 * 4980584 * 2
def baseEnd_4980584 : Nat := 2557433532092846675894717

theorem tailTrace_4980584 : CollatzResearch.WordTrace tailWord_4980584 prefixEnd_4980584 2557433532092846675894717 := by
  unfold tailWord_4980584
  simp only [CollatzResearch.WordTrace]
  refine ⟨90828411094101129435654403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121104548125468172580872537 90828411094101129435654403)
  ·
    refine ⟨136242616641151694153481605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90828411094101129435654403 136242616641151694153481605)
    ·
      refine ⟨25545490620215942653777801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 136242616641151694153481605 25545490620215942653777801)
      ·
        refine ⟨19159117965161956990333351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25545490620215942653777801 19159117965161956990333351)
        ·
          refine ⟨28738676947742935485500027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19159117965161956990333351 28738676947742935485500027)
          ·
            refine ⟨43108015421614403228250041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28738676947742935485500027 43108015421614403228250041)
            ·
              refine ⟨32331011566210802421187531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43108015421614403228250041 32331011566210802421187531)
              ·
                refine ⟨48496517349316203631781297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32331011566210802421187531 48496517349316203631781297)
                ·
                  refine ⟨36372388011987152723835973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48496517349316203631781297 36372388011987152723835973)
                  ·
                    refine ⟨6819822752247591135719245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36372388011987152723835973 6819822752247591135719245)
                    ·
                      refine ⟨2557433532092846675894717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6819822752247591135719245 2557433532092846675894717)
                      ·
                        rfl

theorem cell23_4980584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_4980584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4980584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4980584 prefixEnd_4980584 := by exact prefixLift 4980584
  have htrace : WordTrace (prefixWord ++ tailWord_4980584) baseStart_4980584 baseEnd_4980584 := by
    simpa [prefixWord, tailWord_4980584, baseEnd_4980584] using wordTrace_append hprefix tailTrace_4980584
  have hstable : (prefixWord ++ tailWord_4980584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4980584).length < 2 ^ (prefixWord ++ tailWord_4980584).sum := by decide
  have hdescent : baseEnd_4980584 < baseStart_4980584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4980584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4980624 : List Nat := [2, 1, 1, 1, 1, 1, 2, 4, 1, 7, 2]
def baseStart_4980624 : Nat := 118140960795 + 4980624 * 2 ^ 59
def prefixEnd_4980624 : Nat := 4983230072969 + 3 ^ 40 * 4980624 * 2
def baseEnd_4980624 : Nat := 2557454071319026519394533

theorem tailTrace_4980624 : CollatzResearch.WordTrace tailWord_4980624 prefixEnd_4980624 2557454071319026519394533 := by
  unfold tailWord_4980624
  simp only [CollatzResearch.WordTrace]
  refine ⟨90829140554028672851382463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121105520738704897135176617 90829140554028672851382463)
  ·
    refine ⟨136243710831043009277073695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90829140554028672851382463 136243710831043009277073695)
    ·
      refine ⟨204365566246564513915610543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136243710831043009277073695 204365566246564513915610543)
      ·
        refine ⟨306548349369846770873415815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204365566246564513915610543 306548349369846770873415815)
        ·
          refine ⟨459822524054770156310123723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 306548349369846770873415815 459822524054770156310123723)
          ·
            refine ⟨689733786082155234465185585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 459822524054770156310123723 689733786082155234465185585)
            ·
              refine ⟨517300339561616425848889189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 689733786082155234465185585 517300339561616425848889189)
              ·
                refine ⟨96993813667803079846666723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 517300339561616425848889189 96993813667803079846666723)
                ·
                  refine ⟨145490720501704619770000085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96993813667803079846666723 145490720501704619770000085)
                  ·
                    refine ⟨3409938761758702025859377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 145490720501704619770000085 3409938761758702025859377)
                    ·
                      refine ⟨2557454071319026519394533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3409938761758702025859377 2557454071319026519394533)
                      ·
                        rfl

theorem cell23_4980624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 1, 7, 2].length) (baseStart_4980624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4980624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4980624 prefixEnd_4980624 := by exact prefixLift 4980624
  have htrace : WordTrace (prefixWord ++ tailWord_4980624) baseStart_4980624 baseEnd_4980624 := by
    simpa [prefixWord, tailWord_4980624, baseEnd_4980624] using wordTrace_append hprefix tailTrace_4980624
  have hstable : (prefixWord ++ tailWord_4980624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4980624).length < 2 ^ (prefixWord ++ tailWord_4980624).sum := by decide
  have hdescent : baseEnd_4980624 < baseStart_4980624 := by decide
  rcases family_descends (prefixWord ++ tailWord_4980624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4980632 : List Nat := [2, 1, 2, 6, 1, 1, 2, 2, 2, 2, 2]
def baseStart_4980632 : Nat := 118140960795 + 4980632 * 2 ^ 59
def prefixEnd_4980632 : Nat := 4983230072969 + 3 ^ 40 * 4980632 * 2
def baseEnd_4980632 : Nat := 2557458179164262488094497

theorem tailTrace_4980632 : CollatzResearch.WordTrace tailWord_4980632 prefixEnd_4980632 2557458179164262488094497 := by
  unfold tailWord_4980632
  simp only [CollatzResearch.WordTrace]
  refine ⟨90829286446014181534528075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121105715261352242046037433 90829286446014181534528075)
  ·
    refine ⟨136243929669021272301792113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90829286446014181534528075 136243929669021272301792113)
    ·
      refine ⟨102182947251765954226344085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136243929669021272301792113 102182947251765954226344085)
      ·
        refine ⟨4789825652426529104359879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 102182947251765954226344085 4789825652426529104359879)
        ·
          refine ⟨7184738478639793656539819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4789825652426529104359879 7184738478639793656539819)
          ·
            refine ⟨10777107717959690484809729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7184738478639793656539819 10777107717959690484809729)
            ·
              refine ⟨8082830788469767863607297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10777107717959690484809729 8082830788469767863607297)
              ·
                refine ⟨6062123091352325897705473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8082830788469767863607297 6062123091352325897705473)
                ·
                  refine ⟨4546592318514244423279105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6062123091352325897705473 4546592318514244423279105)
                  ·
                    refine ⟨3409944238885683317459329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4546592318514244423279105 3409944238885683317459329)
                    ·
                      refine ⟨2557458179164262488094497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3409944238885683317459329 2557458179164262488094497)
                      ·
                        rfl

theorem cell23_4980632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_4980632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4980632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4980632 prefixEnd_4980632 := by exact prefixLift 4980632
  have htrace : WordTrace (prefixWord ++ tailWord_4980632) baseStart_4980632 baseEnd_4980632 := by
    simpa [prefixWord, tailWord_4980632, baseEnd_4980632] using wordTrace_append hprefix tailTrace_4980632
  have hstable : (prefixWord ++ tailWord_4980632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4980632).length < 2 ^ (prefixWord ++ tailWord_4980632).sum := by decide
  have hdescent : baseEnd_4980632 < baseStart_4980632 := by decide
  rcases family_descends (prefixWord ++ tailWord_4980632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4980644 : List Nat := [2, 3, 1, 2, 1, 3, 2, 1, 1, 2, 5]
def baseStart_4980644 : Nat := 118140960795 + 4980644 * 2 ^ 59
def prefixEnd_4980644 : Nat := 4983230072969 + 3 ^ 40 * 4980644 * 2
def baseEnd_4980644 : Nat := 2557464340932116441144441

theorem tailTrace_4980644 : CollatzResearch.WordTrace tailWord_4980644 prefixEnd_4980644 2557464340932116441144441 := by
  unfold tailWord_4980644
  simp only [CollatzResearch.WordTrace]
  refine ⟨90829505283992444559246493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121106007045323259412328657 90829505283992444559246493)
  ·
    refine ⟨34061064481497166709717435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90829505283992444559246493 34061064481497166709717435)
    ·
      refine ⟨51091596722245750064576153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34061064481497166709717435 51091596722245750064576153)
      ·
        refine ⟨38318697541684312548432115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51091596722245750064576153 38318697541684312548432115)
        ·
          refine ⟨57478046312526468822648173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38318697541684312548432115 57478046312526468822648173)
          ·
            refine ⟨21554267367197425808493065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57478046312526468822648173 21554267367197425808493065)
            ·
              refine ⟨16165700525398069356369799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21554267367197425808493065 16165700525398069356369799)
              ·
                refine ⟨24248550788097104034554699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16165700525398069356369799 24248550788097104034554699)
                ·
                  refine ⟨36372826182145656051832049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24248550788097104034554699 36372826182145656051832049)
                  ·
                    refine ⟨27279619636609242038874037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36372826182145656051832049 27279619636609242038874037)
                    ·
                      refine ⟨2557464340932116441144441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27279619636609242038874037 2557464340932116441144441)
                      ·
                        rfl

theorem cell23_4980644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_4980644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4980644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4980644 prefixEnd_4980644 := by exact prefixLift 4980644
  have htrace : WordTrace (prefixWord ++ tailWord_4980644) baseStart_4980644 baseEnd_4980644 := by
    simpa [prefixWord, tailWord_4980644, baseEnd_4980644] using wordTrace_append hprefix tailTrace_4980644
  have hstable : (prefixWord ++ tailWord_4980644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4980644).length < 2 ^ (prefixWord ++ tailWord_4980644).sum := by decide
  have hdescent : baseEnd_4980644 < baseStart_4980644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4980644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4980667 : List Nat := [1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 6]
def baseStart_4980667 : Nat := 118140960795 + 4980667 * 2 ^ 59
def prefixEnd_4980667 : Nat := 4983230072969 + 3 ^ 40 * 4980667 * 2
def baseEnd_4980667 : Nat := 2557476150987169851156835

theorem tailTrace_4980667 : CollatzResearch.WordTrace tailWord_4980667 prefixEnd_4980667 2557476150987169851156835 := by
  unfold tailWord_4980667
  simp only [CollatzResearch.WordTrace]
  refine ⟨181659849446901564046580255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121106566297934376031053503 181659849446901564046580255)
  ·
    refine ⟨272489774170352346069870383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181659849446901564046580255 272489774170352346069870383)
    ·
      refine ⟨408734661255528519104805575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272489774170352346069870383 408734661255528519104805575)
      ·
        refine ⟨613101991883292778657208363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 408734661255528519104805575 613101991883292778657208363)
        ·
          refine ⟨919652987824939167985812545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 613101991883292778657208363 919652987824939167985812545)
          ·
            refine ⟨689739740868704375989359409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 919652987824939167985812545 689739740868704375989359409)
            ·
              refine ⟨517304805651528281992019557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 689739740868704375989359409 517304805651528281992019557)
              ·
                refine ⟨96994651059661552873503667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 517304805651528281992019557 96994651059661552873503667)
                ·
                  refine ⟨145491976589492329310255501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96994651059661552873503667 145491976589492329310255501)
                  ·
                    refine ⟨54559491221059623491345813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 145491976589492329310255501 54559491221059623491345813)
                    ·
                      refine ⟨2557476150987169851156835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54559491221059623491345813 2557476150987169851156835)
                      ·
                        rfl

theorem cell23_4980667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 6].length) (baseStart_4980667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4980667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4980667 prefixEnd_4980667 := by exact prefixLift 4980667
  have htrace : WordTrace (prefixWord ++ tailWord_4980667) baseStart_4980667 baseEnd_4980667 := by
    simpa [prefixWord, tailWord_4980667, baseEnd_4980667] using wordTrace_append hprefix tailTrace_4980667
  have hstable : (prefixWord ++ tailWord_4980667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4980667).length < 2 ^ (prefixWord ++ tailWord_4980667).sum := by decide
  have hdescent : baseEnd_4980667 < baseStart_4980667 := by decide
  rcases family_descends (prefixWord ++ tailWord_4980667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4980684 : List Nat := [2, 2, 1, 4, 1, 2, 1, 1, 2, 1, 6]
def baseStart_4980684 : Nat := 118140960795 + 4980684 * 2 ^ 59
def prefixEnd_4980684 : Nat := 4983230072969 + 3 ^ 40 * 4980684 * 2
def baseEnd_4980684 : Nat := 2557484880158296284644257

theorem tailTrace_4980684 : CollatzResearch.WordTrace tailWord_4980684 prefixEnd_4980684 2557484880158296284644257 := by
  unfold tailWord_4980684
  simp only [CollatzResearch.WordTrace]
  refine ⟨90830234743919987974974553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121106979658559983966632737 90830234743919987974974553)
  ·
    refine ⟨68122676057939990981230915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90830234743919987974974553 68122676057939990981230915)
    ·
      refine ⟨102184014086909986471846373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68122676057939990981230915 102184014086909986471846373)
      ·
        refine ⟨19159502641295622463471195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102184014086909986471846373 19159502641295622463471195)
        ·
          refine ⟨28739253961943433695206793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19159502641295622463471195 28739253961943433695206793)
          ·
            refine ⟨21554440471457575271405095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28739253961943433695206793 21554440471457575271405095)
            ·
              refine ⟨32331660707186362907107643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21554440471457575271405095 32331660707186362907107643)
              ·
                refine ⟨48497491060779544360661465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32331660707186362907107643 48497491060779544360661465)
                ·
                  refine ⟨36373118295584658270496099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48497491060779544360661465 36373118295584658270496099)
                  ·
                    refine ⟨54559677443376987405744149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36373118295584658270496099 54559677443376987405744149)
                    ·
                      refine ⟨2557484880158296284644257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54559677443376987405744149 2557484880158296284644257)
                      ·
                        rfl

theorem cell23_4980684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_4980684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4980684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4980684 prefixEnd_4980684 := by exact prefixLift 4980684
  have htrace : WordTrace (prefixWord ++ tailWord_4980684) baseStart_4980684 baseEnd_4980684 := by
    simpa [prefixWord, tailWord_4980684, baseEnd_4980684] using wordTrace_append hprefix tailTrace_4980684
  have hstable : (prefixWord ++ tailWord_4980684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4980684).length < 2 ^ (prefixWord ++ tailWord_4980684).sum := by decide
  have hdescent : baseEnd_4980684 < baseStart_4980684 := by decide
  rcases family_descends (prefixWord ++ tailWord_4980684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4980698 : List Nat := [3, 1, 1, 2, 5, 1, 2, 1, 3, 4]
def baseStart_4980698 : Nat := 118140960795 + 4980698 * 2 ^ 59
def prefixEnd_4980698 : Nat := 4983230072969 + 3 ^ 40 * 4980698 * 2
def baseEnd_4980698 : Nat := 852497356295819743289731

theorem tailTrace_4980698 : CollatzResearch.WordTrace tailWord_4980698 prefixEnd_4980698 852497356295819743289731 := by
  unfold tailWord_4980698
  simp only [CollatzResearch.WordTrace]
  refine ⟨45415245027447314085239687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121107320073192837560639165 45415245027447314085239687)
  ·
    refine ⟨68122867541170971127859531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45415245027447314085239687 68122867541170971127859531)
    ·
      refine ⟨102184301311756456691789297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68122867541170971127859531 102184301311756456691789297)
      ·
        refine ⟨76638225983817342518841973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102184301311756456691789297 76638225983817342518841973)
        ·
          refine ⟨7184833685982875861141435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76638225983817342518841973 7184833685982875861141435)
          ·
            refine ⟨10777250528974313791712153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7184833685982875861141435 10777250528974313791712153)
            ·
              refine ⟨8082937896730735343784115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10777250528974313791712153 8082937896730735343784115)
              ·
                refine ⟨12124406845096103015676173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8082937896730735343784115 12124406845096103015676173)
                ·
                  refine ⟨4546652566911038630878565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12124406845096103015676173 4546652566911038630878565)
                  ·
                    refine ⟨852497356295819743289731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4546652566911038630878565 852497356295819743289731)
                    ·
                      rfl

theorem cell23_4980698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 1, 3, 4].length) (baseStart_4980698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4980698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4980698 prefixEnd_4980698 := by exact prefixLift 4980698
  have htrace : WordTrace (prefixWord ++ tailWord_4980698) baseStart_4980698 baseEnd_4980698 := by
    simpa [prefixWord, tailWord_4980698, baseEnd_4980698] using wordTrace_append hprefix tailTrace_4980698
  have hstable : (prefixWord ++ tailWord_4980698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4980698).length < 2 ^ (prefixWord ++ tailWord_4980698).sum := by decide
  have hdescent : baseEnd_4980698 < baseStart_4980698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4980698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4980714 : List Nat := [3, 1, 3, 1, 2, 1, 1, 2, 1, 2, 6]
def baseStart_4980714 : Nat := 118140960795 + 4980714 * 2 ^ 59
def prefixEnd_4980714 : Nat := 4983230072969 + 3 ^ 40 * 4980714 * 2
def baseEnd_4980714 : Nat := 2557500284577931167269119

theorem tailTrace_4980714 : CollatzResearch.WordTrace tailWord_4980714 prefixEnd_4980714 2557500284577931167269119 := by
  unfold tailWord_4980714
  simp only [CollatzResearch.WordTrace]
  refine ⟨45415390919432822768385299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121107709118487527382360797 45415390919432822768385299)
  ·
    refine ⟨68123086379149234152577949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45415390919432822768385299 68123086379149234152577949)
    ·
      refine ⟨25546157392180962807216731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68123086379149234152577949 25546157392180962807216731)
      ·
        refine ⟨38319236088271444210825097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25546157392180962807216731 38319236088271444210825097)
        ·
          refine ⟨28739427066203583158118823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38319236088271444210825097 28739427066203583158118823)
          ·
            refine ⟨43109140599305374737178235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28739427066203583158118823 43109140599305374737178235)
            ·
              refine ⟨64663710898958062105767353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43109140599305374737178235 64663710898958062105767353)
              ·
                refine ⟨48497783174218546579325515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64663710898958062105767353 48497783174218546579325515)
                ·
                  refine ⟨72746674761327819868988273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48497783174218546579325515 72746674761327819868988273)
                  ·
                    refine ⟨54560006070995864901741205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 72746674761327819868988273 54560006070995864901741205)
                    ·
                      refine ⟨2557500284577931167269119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54560006070995864901741205 2557500284577931167269119)
                      ·
                        rfl

theorem cell23_4980714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_4980714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4980714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4980714 prefixEnd_4980714 := by exact prefixLift 4980714
  have htrace : WordTrace (prefixWord ++ tailWord_4980714) baseStart_4980714 baseEnd_4980714 := by
    simpa [prefixWord, tailWord_4980714, baseEnd_4980714] using wordTrace_append hprefix tailTrace_4980714
  have hstable : (prefixWord ++ tailWord_4980714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4980714).length < 2 ^ (prefixWord ++ tailWord_4980714).sum := by decide
  have hdescent : baseEnd_4980714 < baseStart_4980714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4980714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4980731 : List Nat := [1, 1, 1, 1, 1, 3, 6, 1, 1, 5, 2]
def baseStart_4980731 : Nat := 118140960795 + 4980731 * 2 ^ 59
def prefixEnd_4980731 : Nat := 4983230072969 + 3 ^ 40 * 4980731 * 2
def baseEnd_4980731 : Nat := 2557509013749057600756541

theorem tailTrace_4980731 : CollatzResearch.WordTrace tailWord_4980731 prefixEnd_4980731 2557509013749057600756541 := by
  unfold tailWord_4980731
  simp only [CollatzResearch.WordTrace]
  refine ⟨181662183718669702976910047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121108122479113135317940031 181662183718669702976910047)
  ·
    refine ⟨272493275578004554465365071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181662183718669702976910047 272493275578004554465365071)
    ·
      refine ⟨408739913367006831698047607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272493275578004554465365071 408739913367006831698047607)
      ·
        refine ⟨613109870050510247547071411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 408739913367006831698047607 613109870050510247547071411)
        ·
          refine ⟨919664805075765371320607117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 613109870050510247547071411 919664805075765371320607117)
          ·
            refine ⟨344874301903412014245227669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 919664805075765371320607117 344874301903412014245227669)
            ·
              refine ⟨16165982901722438167745047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 344874301903412014245227669 16165982901722438167745047)
              ·
                refine ⟨24248974352583657251617571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16165982901722438167745047 24248974352583657251617571)
                ·
                  refine ⟨36373461528875485877426357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24248974352583657251617571 36373461528875485877426357)
                  ·
                    refine ⟨3410012018332076801008721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36373461528875485877426357 3410012018332076801008721)
                    ·
                      refine ⟨2557509013749057600756541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3410012018332076801008721 2557509013749057600756541)
                      ·
                        rfl

theorem cell23_4980731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 5, 2].length) (baseStart_4980731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4980731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4980731 prefixEnd_4980731 := by exact prefixLift 4980731
  have htrace : WordTrace (prefixWord ++ tailWord_4980731) baseStart_4980731 baseEnd_4980731 := by
    simpa [prefixWord, tailWord_4980731, baseEnd_4980731] using wordTrace_append hprefix tailTrace_4980731
  have hstable : (prefixWord ++ tailWord_4980731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4980731).length < 2 ^ (prefixWord ++ tailWord_4980731).sum := by decide
  have hdescent : baseEnd_4980731 < baseStart_4980731 := by decide
  rcases family_descends (prefixWord ++ tailWord_4980731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4980741 : List Nat := [1, 3, 1, 1, 2, 4, 2, 3, 1, 5]
def baseStart_4980741 : Nat := 118140960795 + 4980741 * 2 ^ 59
def prefixEnd_4980741 : Nat := 4983230072969 + 3 ^ 40 * 4980741 * 2
def baseEnd_4980741 : Nat := 852504716185200853877165

theorem tailTrace_4980741 : CollatzResearch.WordTrace tailWord_4980741 prefixEnd_4980741 852504716185200853877165 := by
  unfold tailWord_4980741
  simp only [CollatzResearch.WordTrace]
  refine ⟨181662548448633474684774077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121108365632422316456516051 181662548448633474684774077)
  ·
    refine ⟨68123455668237553006790279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181662548448633474684774077 68123455668237553006790279)
    ·
      refine ⟨102185183502356329510185419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68123455668237553006790279 102185183502356329510185419)
      ·
        refine ⟨153277775253534494265278129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102185183502356329510185419 153277775253534494265278129)
        ·
          refine ⟨114958331440150870698958597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153277775253534494265278129 114958331440150870698958597)
          ·
            refine ⟨21554687145028288256054737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 114958331440150870698958597 21554687145028288256054737)
            ·
              refine ⟨16166015358771216192041053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21554687145028288256054737 16166015358771216192041053)
              ·
                refine ⟨6062255759539206072015395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16166015358771216192041053 6062255759539206072015395)
                ·
                  refine ⟨9093383639308809108023093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6062255759539206072015395 9093383639308809108023093)
                  ·
                    refine ⟨852504716185200853877165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9093383639308809108023093 852504716185200853877165)
                    ·
                      rfl

theorem cell23_4980741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 3, 1, 5].length) (baseStart_4980741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4980741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4980741 prefixEnd_4980741 := by exact prefixLift 4980741
  have htrace : WordTrace (prefixWord ++ tailWord_4980741) baseStart_4980741 baseEnd_4980741 := by
    simpa [prefixWord, tailWord_4980741, baseEnd_4980741] using wordTrace_append hprefix tailTrace_4980741
  have hstable : (prefixWord ++ tailWord_4980741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4980741).length < 2 ^ (prefixWord ++ tailWord_4980741).sum := by decide
  have hdescent : baseEnd_4980741 < baseStart_4980741 := by decide
  rcases family_descends (prefixWord ++ tailWord_4980741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4980748 : List Nat := [2, 2, 1, 2, 3, 1, 3, 2, 2, 3, 2]
def baseStart_4980748 : Nat := 118140960795 + 4980748 * 2 ^ 59
def prefixEnd_4980748 : Nat := 4983230072969 + 3 ^ 40 * 4980748 * 2
def baseEnd_4980748 : Nat := 2557517742920184034243963

theorem tailTrace_4980748 : CollatzResearch.WordTrace tailWord_4980748 prefixEnd_4980748 2557517742920184034243963 := by
  unfold tailWord_4980748
  simp only [CollatzResearch.WordTrace]
  refine ⟨90831401879804057440139449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121108535839738743253519265 90831401879804057440139449)
  ·
    refine ⟨68123551409853043080104587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90831401879804057440139449 68123551409853043080104587)
    ·
      refine ⟨102185327114779564620156881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68123551409853043080104587 102185327114779564620156881)
      ·
        refine ⟨76638995336084673465117661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102185327114779564620156881 76638995336084673465117661)
        ·
          refine ⟨28739623251031752549419123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76638995336084673465117661 28739623251031752549419123)
          ·
            refine ⟨43109434876547628824128685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28739623251031752549419123 43109434876547628824128685)
            ·
              refine ⟨16166038078705360809048257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43109434876547628824128685 16166038078705360809048257)
              ·
                refine ⟨12124528559029020606786193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16166038078705360809048257 12124528559029020606786193)
                ·
                  refine ⟨9093396419271765455089645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12124528559029020606786193 9093396419271765455089645)
                  ·
                    refine ⟨3410023657226912045658617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9093396419271765455089645 3410023657226912045658617)
                    ·
                      refine ⟨2557517742920184034243963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3410023657226912045658617 2557517742920184034243963)
                      ·
                        rfl

theorem cell23_4980748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 2, 3, 2].length) (baseStart_4980748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4980748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4980748 prefixEnd_4980748 := by exact prefixLift 4980748
  have htrace : WordTrace (prefixWord ++ tailWord_4980748) baseStart_4980748 baseEnd_4980748 := by
    simpa [prefixWord, tailWord_4980748, baseEnd_4980748] using wordTrace_append hprefix tailTrace_4980748
  have hstable : (prefixWord ++ tailWord_4980748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4980748).length < 2 ^ (prefixWord ++ tailWord_4980748).sum := by decide
  have hdescent : baseEnd_4980748 < baseStart_4980748 := by decide
  rcases family_descends (prefixWord ++ tailWord_4980748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4980749 : List Nat := [1, 7, 1, 2, 1, 2, 1, 1, 3, 4]
def baseStart_4980749 : Nat := 118140960795 + 4980749 * 2 ^ 59
def prefixEnd_4980749 : Nat := 4983230072969 + 3 ^ 40 * 4980749 * 2
def baseEnd_4980749 : Nat := 852506085466946176777153

theorem tailTrace_4980749 : CollatzResearch.WordTrace tailWord_4980749 prefixEnd_4980749 852506085466946176777153 := by
  unfold tailWord_4980749
  simp only [CollatzResearch.WordTrace]
  refine ⟨181662840232604492051065301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121108560155069661367376867 181662840232604492051065301)
  ·
    refine ⟨4257722817951667782446843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 181662840232604492051065301 4257722817951667782446843)
    ·
      refine ⟨6386584226927501673670265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4257722817951667782446843 6386584226927501673670265)
      ·
        refine ⟨4789938170195626255252699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6386584226927501673670265 4789938170195626255252699)
        ·
          refine ⟨7184907255293439382879049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4789938170195626255252699 7184907255293439382879049)
          ·
            refine ⟨5388680441470079537159287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7184907255293439382879049 5388680441470079537159287)
            ·
              refine ⟨8083020662205119305738931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5388680441470079537159287 8083020662205119305738931)
              ·
                refine ⟨12124530993307678958608397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8083020662205119305738931 12124530993307678958608397)
                ·
                  refine ⟨4546699122490379609478149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12124530993307678958608397 4546699122490379609478149)
                  ·
                    refine ⟨852506085466946176777153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4546699122490379609478149 852506085466946176777153)
                    ·
                      rfl

theorem cell23_4980749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_4980749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4980749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4980749 prefixEnd_4980749 := by exact prefixLift 4980749
  have htrace : WordTrace (prefixWord ++ tailWord_4980749) baseStart_4980749 baseEnd_4980749 := by
    simpa [prefixWord, tailWord_4980749, baseEnd_4980749] using wordTrace_append hprefix tailTrace_4980749
  have hstable : (prefixWord ++ tailWord_4980749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4980749).length < 2 ^ (prefixWord ++ tailWord_4980749).sum := by decide
  have hdescent : baseEnd_4980749 < baseStart_4980749 := by decide
  rcases family_descends (prefixWord ++ tailWord_4980749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4980778 : List Nat := [3, 1, 4, 1, 2, 2, 1, 1, 3, 1, 4]
def baseStart_4980778 : Nat := 118140960795 + 4980778 * 2 ^ 59
def prefixEnd_4980778 : Nat := 4983230072969 + 3 ^ 40 * 4980778 * 2
def baseEnd_4980778 : Nat := 2557533147339818916868825

theorem tailTrace_4980778 : CollatzResearch.WordTrace tailWord_4980778 prefixEnd_4980778 2557533147339818916868825 := by
  unfold tailWord_4980778
  simp only [CollatzResearch.WordTrace]
  refine ⟨45415974487374857500967747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121109265299666286669247325 45415974487374857500967747)
  ·
    refine ⟨68123961731062286251451621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45415974487374857500967747 68123961731062286251451621)
    ·
      refine ⟨12773242824574178672147179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68123961731062286251451621 12773242824574178672147179)
      ·
        refine ⟨19159864236861268008220769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12773242824574178672147179 19159864236861268008220769)
        ·
          refine ⟨14369898177645951006165577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19159864236861268008220769 14369898177645951006165577)
          ·
            refine ⟨10777423633234463254624183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14369898177645951006165577 10777423633234463254624183)
            ·
              refine ⟨16166135449851694881936275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10777423633234463254624183 16166135449851694881936275)
              ·
                refine ⟨24249203174777542322904413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16166135449851694881936275 24249203174777542322904413)
                ·
                  refine ⟨9093451190541578371089155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24249203174777542322904413 9093451190541578371089155)
                  ·
                    refine ⟨13640176785812367556633733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9093451190541578371089155 13640176785812367556633733)
                    ·
                      refine ⟨2557533147339818916868825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13640176785812367556633733 2557533147339818916868825)
                      ·
                        rfl

theorem cell23_4980778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_4980778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4980778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4980778 prefixEnd_4980778 := by exact prefixLift 4980778
  have htrace : WordTrace (prefixWord ++ tailWord_4980778) baseStart_4980778 baseEnd_4980778 := by
    simpa [prefixWord, tailWord_4980778, baseEnd_4980778] using wordTrace_append hprefix tailTrace_4980778
  have hstable : (prefixWord ++ tailWord_4980778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4980778).length < 2 ^ (prefixWord ++ tailWord_4980778).sum := by decide
  have hdescent : baseEnd_4980778 < baseStart_4980778 := by decide
  rcases family_descends (prefixWord ++ tailWord_4980778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4980784 : List Nat := [2, 1, 1, 1, 2, 5, 2, 9]
def baseStart_4980784 : Nat := 118140960795 + 4980784 * 2 ^ 59
def prefixEnd_4980784 : Nat := 4983230072969 + 3 ^ 40 * 4980784 * 2
def baseEnd_4980784 : Nat := 94723564008286884940511

theorem tailTrace_4980784 : CollatzResearch.WordTrace tailWord_4980784 prefixEnd_4980784 94723564008286884940511 := by
  unfold tailWord_4980784
  simp only [CollatzResearch.WordTrace]
  refine ⟨90832058393738846514294703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121109411191651795352392937 90832058393738846514294703)
  ·
    refine ⟨136248087590608269771442055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90832058393738846514294703 136248087590608269771442055)
    ·
      refine ⟨204372131385912404657163083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136248087590608269771442055 204372131385912404657163083)
      ·
        refine ⟨306558197078868606985744625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204372131385912404657163083 306558197078868606985744625)
        ·
          refine ⟨229918647809151455239308469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 306558197078868606985744625 229918647809151455239308469)
          ·
            refine ⟨21554873232107948928685169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 229918647809151455239308469 21554873232107948928685169)
            ·
              refine ⟨16166154924080961696513877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21554873232107948928685169 16166154924080961696513877)
              ·
                refine ⟨94723564008286884940511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16166154924080961696513877 94723564008286884940511)
                ·
                  rfl

theorem cell23_4980784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 9].length) (baseStart_4980784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4980784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4980784 prefixEnd_4980784 := by exact prefixLift 4980784
  have htrace : WordTrace (prefixWord ++ tailWord_4980784) baseStart_4980784 baseEnd_4980784 := by
    simpa [prefixWord, tailWord_4980784, baseEnd_4980784] using wordTrace_append hprefix tailTrace_4980784
  have hstable : (prefixWord ++ tailWord_4980784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4980784).length < 2 ^ (prefixWord ++ tailWord_4980784).sum := by decide
  have hdescent : baseEnd_4980784 < baseStart_4980784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4980784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4980818 : List Nat := [3, 2, 2, 1, 4, 2, 1, 8]
def baseStart_4980818 : Nat := 118140960795 + 4980818 * 2 ^ 59
def prefixEnd_4980818 : Nat := 4983230072969 + 3 ^ 40 * 4980818 * 2
def baseEnd_4980818 : Nat := 94724210613555509643283

theorem tailTrace_4980818 : CollatzResearch.WordTrace tailWord_4980818 prefixEnd_4980818 94724210613555509643283 := by
  unfold tailWord_4980818
  simp only [CollatzResearch.WordTrace]
  refine ⟨45416339217338629208831777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121110237912903011223551405 45416339217338629208831777)
  ·
    refine ⟨34062254413003971906623833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45416339217338629208831777 34062254413003971906623833)
    ·
      refine ⟨25546690809752978929967875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34062254413003971906623833 25546690809752978929967875)
      ·
        refine ⟨38320036214629468394951813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25546690809752978929967875 38320036214629468394951813)
        ·
          refine ⟨7185006790243025324053465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38320036214629468394951813 7185006790243025324053465)
          ·
            refine ⟨5388755092682268993040099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7185006790243025324053465 5388755092682268993040099)
            ·
              refine ⟨8083132639023403489560149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5388755092682268993040099 8083132639023403489560149)
              ·
                refine ⟨94724210613555509643283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8083132639023403489560149 94724210613555509643283)
                ·
                  rfl

theorem cell23_4980818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 8].length) (baseStart_4980818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4980818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4980818 prefixEnd_4980818 := by exact prefixLift 4980818
  have htrace : WordTrace (prefixWord ++ tailWord_4980818) baseStart_4980818 baseEnd_4980818 := by
    simpa [prefixWord, tailWord_4980818, baseEnd_4980818] using wordTrace_append hprefix tailTrace_4980818
  have hstable : (prefixWord ++ tailWord_4980818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4980818).length < 2 ^ (prefixWord ++ tailWord_4980818).sum := by decide
  have hdescent : baseEnd_4980818 < baseStart_4980818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4980818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4980822 : List Nat := [5, 2, 2, 1, 1, 1, 2, 3, 2, 4]
def baseStart_4980822 : Nat := 118140960795 + 4980822 * 2 ^ 59
def prefixEnd_4980822 : Nat := 4983230072969 + 3 ^ 40 * 4980822 * 2
def baseEnd_4980822 : Nat := 852518580162872248239541

theorem tailTrace_4980822 : CollatzResearch.WordTrace tailWord_4980822 prefixEnd_4980822 852518580162872248239541 := by
  unfold tailWord_4980822
  simp only [CollatzResearch.WordTrace]
  refine ⟨11354093922583751594904545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 121110335174226683678981813 11354093922583751594904545)
  ·
    refine ⟨8515570441937813696178409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11354093922583751594904545 8515570441937813696178409)
    ·
      refine ⟨6386677831453360272133807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8515570441937813696178409 6386677831453360272133807)
      ·
        refine ⟨9580016747180040408200711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6386677831453360272133807 9580016747180040408200711)
        ·
          refine ⟨14370025120770060612301067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9580016747180040408200711 14370025120770060612301067)
          ·
            refine ⟨21555037681155090918451601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14370025120770060612301067 21555037681155090918451601)
            ·
              refine ⟨16166278260866318188838701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21555037681155090918451601 16166278260866318188838701)
              ·
                refine ⟨6062354347824869320814513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16166278260866318188838701 6062354347824869320814513)
                ·
                  refine ⟨4546765760868651990610885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6062354347824869320814513 4546765760868651990610885)
                  ·
                    refine ⟨852518580162872248239541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4546765760868651990610885 852518580162872248239541)
                    ·
                      rfl

theorem cell23_4980822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_4980822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4980822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4980822 prefixEnd_4980822 := by exact prefixLift 4980822
  have htrace : WordTrace (prefixWord ++ tailWord_4980822) baseStart_4980822 baseEnd_4980822 := by
    simpa [prefixWord, tailWord_4980822, baseEnd_4980822] using wordTrace_append hprefix tailTrace_4980822
  have hstable : (prefixWord ++ tailWord_4980822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4980822).length < 2 ^ (prefixWord ++ tailWord_4980822).sum := by decide
  have hdescent : baseEnd_4980822 < baseStart_4980822 := by decide
  rcases family_descends (prefixWord ++ tailWord_4980822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4980828 : List Nat := [2, 2, 4, 1, 1, 2, 1, 3, 1, 3, 3]
def baseStart_4980828 : Nat := 118140960795 + 4980828 * 2 ^ 59
def prefixEnd_4980828 : Nat := 4983230072969 + 3 ^ 40 * 4980828 * 2
def baseEnd_4980828 : Nat := 2557558821372543721243595

theorem tailTrace_4980828 : CollatzResearch.WordTrace tailWord_4980828 prefixEnd_4980828 2557558821372543721243595 := by
  unfold tailWord_4980828
  simp only [CollatzResearch.WordTrace]
  refine ⟨90832860799659144271595569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121110481066212192362127425 90832860799659144271595569)
  ·
    refine ⟨68124645599744358203696677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90832860799659144271595569 68124645599744358203696677)
    ·
      refine ⟨12773371049952067163193127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68124645599744358203696677 12773371049952067163193127)
      ·
        refine ⟨19160056574928100744789691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12773371049952067163193127 19160056574928100744789691)
        ·
          refine ⟨28740084862392151117184537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19160056574928100744789691 28740084862392151117184537)
          ·
            refine ⟨21555063646794113337888403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28740084862392151117184537 21555063646794113337888403)
            ·
              refine ⟨32332595470191170006832605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21555063646794113337888403 32332595470191170006832605)
              ·
                refine ⟨12124723301321688752562227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32332595470191170006832605 12124723301321688752562227)
                ·
                  refine ⟨18187084951982533128843341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12124723301321688752562227 18187084951982533128843341)
                  ·
                    refine ⟨6820156856993449923316253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18187084951982533128843341 6820156856993449923316253)
                    ·
                      refine ⟨2557558821372543721243595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6820156856993449923316253 2557558821372543721243595)
                      ·
                        rfl

theorem cell23_4980828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_4980828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4980828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4980828 prefixEnd_4980828 := by exact prefixLift 4980828
  have htrace : WordTrace (prefixWord ++ tailWord_4980828) baseStart_4980828 baseEnd_4980828 := by
    simpa [prefixWord, tailWord_4980828, baseEnd_4980828] using wordTrace_append hprefix tailTrace_4980828
  have hstable : (prefixWord ++ tailWord_4980828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4980828).length < 2 ^ (prefixWord ++ tailWord_4980828).sum := by decide
  have hdescent : baseEnd_4980828 < baseStart_4980828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4980828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4980855 : List Nat := [1, 1, 3, 1, 1, 6, 1, 3, 1, 3, 2]
def baseStart_4980855 : Nat := 118140960795 + 4980855 * 2 ^ 59
def prefixEnd_4980855 : Nat := 4983230072969 + 3 ^ 40 * 4980855 * 2
def baseEnd_4980855 : Nat := 2557572685350215115605971

theorem tailTrace_4980855 : CollatzResearch.WordTrace tailWord_4980855 prefixEnd_4980855 2557572685350215115605971 := by
  unfold tailWord_4980855
  simp only [CollatzResearch.WordTrace]
  refine ⟨181666706370220472154424019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121111137580146981436282679 181666706370220472154424019)
  ·
    refine ⟨272500059555330708231636029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181666706370220472154424019 272500059555330708231636029)
    ·
      refine ⟨102187522333249015586863511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 272500059555330708231636029 102187522333249015586863511)
      ·
        refine ⟨153281283499873523380295267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102187522333249015586863511 153281283499873523380295267)
        ·
          refine ⟨229921925249810285070442901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153281283499873523380295267 229921925249810285070442901)
          ·
            refine ⟨10777590246084857112677011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 229921925249810285070442901 10777590246084857112677011)
            ·
              refine ⟨16166385369127285669015517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10777590246084857112677011 16166385369127285669015517)
              ·
                refine ⟨6062394513422732125880819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16166385369127285669015517 6062394513422732125880819)
                ·
                  refine ⟨9093591770134098188821229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6062394513422732125880819 9093591770134098188821229)
                  ·
                    refine ⟨3410096913800286820807961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9093591770134098188821229 3410096913800286820807961)
                    ·
                      refine ⟨2557572685350215115605971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3410096913800286820807961 2557572685350215115605971)
                      ·
                        rfl

theorem cell23_4980855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 3, 1, 3, 2].length) (baseStart_4980855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4980855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4980855 prefixEnd_4980855 := by exact prefixLift 4980855
  have htrace : WordTrace (prefixWord ++ tailWord_4980855) baseStart_4980855 baseEnd_4980855 := by
    simpa [prefixWord, tailWord_4980855, baseEnd_4980855] using wordTrace_append hprefix tailTrace_4980855
  have hstable : (prefixWord ++ tailWord_4980855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4980855).length < 2 ^ (prefixWord ++ tailWord_4980855).sum := by decide
  have hdescent : baseEnd_4980855 < baseStart_4980855 := by decide
  rcases family_descends (prefixWord ++ tailWord_4980855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4980861 : List Nat := [1, 4, 1, 1, 3, 2, 1, 2, 2, 6]
def baseStart_4980861 : Nat := 118140960795 + 4980861 * 2 ^ 59
def prefixEnd_4980861 : Nat := 4983230072969 + 3 ^ 40 * 4980861 * 2
def baseEnd_4980861 : Nat := 852525255411380697376981

theorem tailTrace_4980861 : CollatzResearch.WordTrace tailWord_4980861 prefixEnd_4980861 852525255411380697376981 := by
  unfold tailWord_4980861
  simp only [CollatzResearch.WordTrace]
  refine ⟨181666925208198735179142437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121111283472132490119428291 181666925208198735179142437)
  ·
    refine ⟨34062548476537262846089207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 181666925208198735179142437 34062548476537262846089207)
    ·
      refine ⟨51093822714805894269133811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34062548476537262846089207 51093822714805894269133811)
      ·
        refine ⟨76640734072208841403700717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51093822714805894269133811 76640734072208841403700717)
        ·
          refine ⟨28740275277078315526387769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76640734072208841403700717 28740275277078315526387769)
          ·
            refine ⟨21555206457808736644790827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28740275277078315526387769 21555206457808736644790827)
            ·
              refine ⟨32332809686713104967186241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21555206457808736644790827 32332809686713104967186241)
              ·
                refine ⟨24249607265034828725389681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32332809686713104967186241 24249607265034828725389681)
                ·
                  refine ⟨18187205448776121544042261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24249607265034828725389681 18187205448776121544042261)
                  ·
                    refine ⟨852525255411380697376981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18187205448776121544042261 852525255411380697376981)
                    ·
                      rfl

theorem cell23_4980861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2, 6].length) (baseStart_4980861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4980861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4980861 prefixEnd_4980861 := by exact prefixLift 4980861
  have htrace : WordTrace (prefixWord ++ tailWord_4980861) baseStart_4980861 baseEnd_4980861 := by
    simpa [prefixWord, tailWord_4980861, baseEnd_4980861] using wordTrace_append hprefix tailTrace_4980861
  have hstable : (prefixWord ++ tailWord_4980861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4980861).length < 2 ^ (prefixWord ++ tailWord_4980861).sum := by decide
  have hdescent : baseEnd_4980861 < baseStart_4980861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4980861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4980871 : List Nat := [1, 1, 4, 2, 1, 1, 2, 1, 1, 6, 3]
def baseStart_4980871 : Nat := 118140960795 + 4980871 * 2 ^ 59
def prefixEnd_4980871 : Nat := 4983230072969 + 3 ^ 40 * 4980871 * 2
def baseEnd_4980871 : Nat := 2557580901040687053005897

theorem tailTrace_4980871 : CollatzResearch.WordTrace tailWord_4980871 prefixEnd_4980871 2557580901040687053005897 := by
  unfold tailWord_4980871
  simp only [CollatzResearch.WordTrace]
  refine ⟨181667289938162506887006467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121111526625441671258004311 181667289938162506887006467)
  ·
    refine ⟨272500934907243760330509701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181667289938162506887006467 272500934907243760330509701)
    ·
      refine ⟨51093925295108205061970569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 272500934907243760330509701 51093925295108205061970569)
      ·
        refine ⟨38320443971331153796477927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51093925295108205061970569 38320443971331153796477927)
        ·
          refine ⟨57480665956996730694716891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38320443971331153796477927 57480665956996730694716891)
          ·
            refine ⟨86220998935495096042075337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57480665956996730694716891 86220998935495096042075337)
            ·
              refine ⟨64665749201621322031556503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86220998935495096042075337 64665749201621322031556503)
              ·
                refine ⟨96998623802431983047334755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64665749201621322031556503 96998623802431983047334755)
                ·
                  refine ⟨145497935703647974571002133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96998623802431983047334755 145497935703647974571002133)
                  ·
                    refine ⟨6820215736108498808015725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 145497935703647974571002133 6820215736108498808015725)
                    ·
                      refine ⟨2557580901040687053005897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6820215736108498808015725 2557580901040687053005897)
                      ·
                        rfl

theorem cell23_4980871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_4980871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4980871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4980871 prefixEnd_4980871 := by exact prefixLift 4980871
  have htrace : WordTrace (prefixWord ++ tailWord_4980871) baseStart_4980871 baseEnd_4980871 := by
    simpa [prefixWord, tailWord_4980871, baseEnd_4980871] using wordTrace_append hprefix tailTrace_4980871
  have hstable : (prefixWord ++ tailWord_4980871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4980871).length < 2 ^ (prefixWord ++ tailWord_4980871).sum := by decide
  have hdescent : baseEnd_4980871 < baseStart_4980871 := by decide
  rcases family_descends (prefixWord ++ tailWord_4980871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4980886 : List Nat := [5, 3, 2, 1, 1, 2, 2, 7]
def baseStart_4980886 : Nat := 118140960795 + 4980886 * 2 ^ 59
def prefixEnd_4980886 : Nat := 4983230072969 + 3 ^ 40 * 4980886 * 2
def baseEnd_4980886 : Nat := 94725503824092759048827

theorem tailTrace_4980886 : CollatzResearch.WordTrace tailWord_4980886 prefixEnd_4980886 94725503824092759048827 := by
  unfold tailWord_4980886
  simp only [CollatzResearch.WordTrace]
  refine ⟨11354239814569260278050157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 121111891355405442965868341 11354239814569260278050157)
  ·
    refine ⟨4257839930463472604268809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11354239814569260278050157 4257839930463472604268809)
    ·
      refine ⟨3193379947847604453201607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4257839930463472604268809 3193379947847604453201607)
      ·
        refine ⟨4790069921771406679802411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3193379947847604453201607 4790069921771406679802411)
        ·
          refine ⟨7185104882657110019703617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4790069921771406679802411 7185104882657110019703617)
          ·
            refine ⟨5388828661992832514777713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7185104882657110019703617 5388828661992832514777713)
            ·
              refine ⟨4041621496494624386083285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5388828661992832514777713 4041621496494624386083285)
              ·
                refine ⟨94725503824092759048827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4041621496494624386083285 94725503824092759048827)
                ·
                  rfl

theorem cell23_4980886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 7].length) (baseStart_4980886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4980886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4980886 prefixEnd_4980886 := by exact prefixLift 4980886
  have htrace : WordTrace (prefixWord ++ tailWord_4980886) baseStart_4980886 baseEnd_4980886 := by
    simpa [prefixWord, tailWord_4980886, baseEnd_4980886] using wordTrace_append hprefix tailTrace_4980886
  have hstable : (prefixWord ++ tailWord_4980886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4980886).length < 2 ^ (prefixWord ++ tailWord_4980886).sum := by decide
  have hdescent : baseEnd_4980886 < baseStart_4980886 := by decide
  rcases family_descends (prefixWord ++ tailWord_4980886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4980971 : List Nat := [1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 6]
def baseStart_4980971 : Nat := 118140960795 + 4980971 * 2 ^ 59
def prefixEnd_4980971 : Nat := 4983230072969 + 3 ^ 40 * 4980971 * 2
def baseEnd_4980971 : Nat := 2557632249106136661755437

theorem tailTrace_4980971 : CollatzResearch.WordTrace tailWord_4980971 prefixEnd_4980971 2557632249106136661755437 := by
  unfold tailWord_4980971
  simp only [CollatzResearch.WordTrace]
  refine ⟨181670937237800223965646767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121113958158533482643764511 181670937237800223965646767)
  ·
    refine ⟨272506405856700335948470151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181670937237800223965646767 272506405856700335948470151)
    ·
      refine ⟨408759608785050503922705227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272506405856700335948470151 408759608785050503922705227)
      ·
        refine ⟨613139413177575755884057841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 408759608785050503922705227 613139413177575755884057841)
        ·
          refine ⟨459854559883181816913043381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 613139413177575755884057841 459854559883181816913043381)
          ·
            refine ⟨43111364989048295335597817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 459854559883181816913043381 43111364989048295335597817)
            ·
              refine ⟨32333523741786221501698363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43111364989048295335597817 32333523741786221501698363)
              ·
                refine ⟨48500285612679332252547545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32333523741786221501698363 48500285612679332252547545)
                ·
                  refine ⟨36375214209509499189410659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48500285612679332252547545 36375214209509499189410659)
                  ·
                    refine ⟨54562821314264248784115989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36375214209509499189410659 54562821314264248784115989)
                    ·
                      refine ⟨2557632249106136661755437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54562821314264248784115989 2557632249106136661755437)
                      ·
                        rfl

theorem cell23_4980971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 6].length) (baseStart_4980971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4980971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4980971 prefixEnd_4980971 := by exact prefixLift 4980971
  have htrace : WordTrace (prefixWord ++ tailWord_4980971) baseStart_4980971 baseEnd_4980971 := by
    simpa [prefixWord, tailWord_4980971, baseEnd_4980971] using wordTrace_append hprefix tailTrace_4980971
  have hstable : (prefixWord ++ tailWord_4980971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4980971).length < 2 ^ (prefixWord ++ tailWord_4980971).sum := by decide
  have hdescent : baseEnd_4980971 < baseStart_4980971 := by decide
  rcases family_descends (prefixWord ++ tailWord_4980971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4981032 : List Nat := [2, 1, 5, 1, 3, 2, 1, 2, 6]
def baseStart_4981032 : Nat := 118140960795 + 4981032 * 2 ^ 59
def prefixEnd_4981032 : Nat := 4983230072969 + 3 ^ 40 * 4981032 * 2
def baseEnd_4981032 : Nat := 284184841269562324788073

theorem tailTrace_4981032 : CollatzResearch.WordTrace tailWord_4981032 prefixEnd_4981032 284184841269562324788073 := by
  unfold tailWord_4981032
  simp only [CollatzResearch.WordTrace]
  refine ⟨90836581045289615691808675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121115441393719487589078233 90836581045289615691808675)
  ·
    refine ⟨136254871567934423537713013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90836581045289615691808675 136254871567934423537713013)
    ·
      refine ⟨12773894209493852206660595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 136254871567934423537713013 12773894209493852206660595)
      ·
        refine ⟨19160841314240778309990893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12773894209493852206660595 19160841314240778309990893)
        ·
          refine ⟨7185315492840291866246585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19160841314240778309990893 7185315492840291866246585)
          ·
            refine ⟨5388986619630218899684939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7185315492840291866246585 5388986619630218899684939)
            ·
              refine ⟨8083479929445328349527409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5388986619630218899684939 8083479929445328349527409)
              ·
                refine ⟨6062609947083996262145557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8083479929445328349527409 6062609947083996262145557)
                ·
                  refine ⟨284184841269562324788073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6062609947083996262145557 284184841269562324788073)
                  ·
                    rfl

theorem cell23_4981032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 2, 6].length) (baseStart_4981032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4981032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4981032 prefixEnd_4981032 := by exact prefixLift 4981032
  have htrace : WordTrace (prefixWord ++ tailWord_4981032) baseStart_4981032 baseEnd_4981032 := by
    simpa [prefixWord, tailWord_4981032, baseEnd_4981032] using wordTrace_append hprefix tailTrace_4981032
  have hstable : (prefixWord ++ tailWord_4981032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4981032).length < 2 ^ (prefixWord ++ tailWord_4981032).sum := by decide
  have hdescent : baseEnd_4981032 < baseStart_4981032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4981032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4981048 : List Nat := [2, 1, 2, 1, 3, 1, 2, 1, 5, 1, 4]
def baseStart_4981048 : Nat := 118140960795 + 4981048 * 2 ^ 59
def prefixEnd_4981048 : Nat := 4983230072969 + 3 ^ 40 * 4981048 * 2
def baseEnd_4981048 : Nat := 2557671787116532860492583

theorem tailTrace_4981048 : CollatzResearch.WordTrace tailWord_4981048 prefixEnd_4981048 2557671787116532860492583 := by
  unfold tailWord_4981048
  simp only [CollatzResearch.WordTrace]
  refine ⟨90836872829260633058099899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121115830439014177410799865 90836872829260633058099899)
  ·
    refine ⟨136255309243890949587149849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90836872829260633058099899 136255309243890949587149849)
    ·
      refine ⟨102191481932918212190362387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136255309243890949587149849 102191481932918212190362387)
      ·
        refine ⟨153287222899377318285543581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102191481932918212190362387 153287222899377318285543581)
        ·
          refine ⟨57482708587266494357078843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153287222899377318285543581 57482708587266494357078843)
          ·
            refine ⟨86224062880899741535618265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57482708587266494357078843 86224062880899741535618265)
            ·
              refine ⟨64668047160674806151713699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86224062880899741535618265 64668047160674806151713699)
              ·
                refine ⟨97002070741012209227570549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64668047160674806151713699 97002070741012209227570549)
                ·
                  refine ⟨9093944131969894615084739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 97002070741012209227570549 9093944131969894615084739)
                  ·
                    refine ⟨13640916197954841922627109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9093944131969894615084739 13640916197954841922627109)
                    ·
                      refine ⟨2557671787116532860492583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13640916197954841922627109 2557671787116532860492583)
                      ·
                        rfl

theorem cell23_4981048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 5, 1, 4].length) (baseStart_4981048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4981048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4981048 prefixEnd_4981048 := by exact prefixLift 4981048
  have htrace : WordTrace (prefixWord ++ tailWord_4981048) baseStart_4981048 baseEnd_4981048 := by
    simpa [prefixWord, tailWord_4981048, baseEnd_4981048] using wordTrace_append hprefix tailTrace_4981048
  have hstable : (prefixWord ++ tailWord_4981048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4981048).length < 2 ^ (prefixWord ++ tailWord_4981048).sum := by decide
  have hdescent : baseEnd_4981048 < baseStart_4981048 := by decide
  rcases family_descends (prefixWord ++ tailWord_4981048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4981068 : List Nat := [2, 2, 1, 3, 2, 1, 1, 2, 3, 1, 5]
def baseStart_4981068 : Nat := 118140960795 + 4981068 * 2 ^ 59
def prefixEnd_4981068 : Nat := 4983230072969 + 3 ^ 40 * 4981068 * 2
def baseEnd_4981068 : Nat := 2557682056729622782242491

theorem tailTrace_4981068 : CollatzResearch.WordTrace tailWord_4981068 prefixEnd_4981068 2557682056729622782242491 := by
  unfold tailWord_4981068
  simp only [CollatzResearch.WordTrace]
  refine ⟨90837237559224404765963929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121116316745632539687951905 90837237559224404765963929)
  ·
    refine ⟨68127928169418303574472947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90837237559224404765963929 68127928169418303574472947)
    ·
      refine ⟨102191892254127455361709421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68127928169418303574472947 102191892254127455361709421)
      ·
        refine ⟨38321959595297795760641033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102191892254127455361709421 38321959595297795760641033)
        ·
          refine ⟨28741469696473346820480775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38321959595297795760641033 28741469696473346820480775)
          ·
            refine ⟨43112204544710020230721163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28741469696473346820480775 43112204544710020230721163)
            ·
              refine ⟨64668306817065030346081745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43112204544710020230721163 64668306817065030346081745)
              ·
                refine ⟨48501230112798772759561309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64668306817065030346081745 48501230112798772759561309)
                ·
                  refine ⟨18187961292299539784835491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48501230112798772759561309 18187961292299539784835491)
                  ·
                    refine ⟨27281941938449309677253237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18187961292299539784835491 27281941938449309677253237)
                    ·
                      refine ⟨2557682056729622782242491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27281941938449309677253237 2557682056729622782242491)
                      ·
                        rfl

theorem cell23_4981068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_4981068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4981068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4981068 prefixEnd_4981068 := by exact prefixLift 4981068
  have htrace : WordTrace (prefixWord ++ tailWord_4981068) baseStart_4981068 baseEnd_4981068 := by
    simpa [prefixWord, tailWord_4981068, baseEnd_4981068] using wordTrace_append hprefix tailTrace_4981068
  have hstable : (prefixWord ++ tailWord_4981068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4981068).length < 2 ^ (prefixWord ++ tailWord_4981068).sum := by decide
  have hdescent : baseEnd_4981068 < baseStart_4981068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4981068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4981076 : List Nat := [2, 4, 1, 1, 2, 4, 1, 3, 1, 1, 3]
def baseStart_4981076 : Nat := 118140960795 + 4981076 * 2 ^ 59
def prefixEnd_4981076 : Nat := 4983230072969 + 3 ^ 40 * 4981076 * 2
def baseEnd_4981076 : Nat := 2557686164574858750942455

theorem tailTrace_4981076 : CollatzResearch.WordTrace tailWord_4981076 prefixEnd_4981076 2557686164574858750942455 := by
  unfold tailWord_4981076
  simp only [CollatzResearch.WordTrace]
  refine ⟨90837383451209913449109541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121116511268279884598812721 90837383451209913449109541)
  ·
    refine ⟨17032009397101858771708039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90837383451209913449109541 17032009397101858771708039)
    ·
      refine ⟨25548014095652788157562059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17032009397101858771708039 25548014095652788157562059)
      ·
        refine ⟨38322021143479182236343089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25548014095652788157562059 38322021143479182236343089)
        ·
          refine ⟨28741515857609386677257317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38322021143479182236343089 28741515857609386677257317)
          ·
            refine ⟨5389034223301760001985747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28741515857609386677257317 5389034223301760001985747)
            ·
              refine ⟨8083551334952640002978621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5389034223301760001985747 8083551334952640002978621)
              ·
                refine ⟨3031331750607240001116983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8083551334952640002978621 3031331750607240001116983)
                ·
                  refine ⟨4546997625910860001675475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3031331750607240001116983 4546997625910860001675475)
                  ·
                    refine ⟨6820496438866290002513213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4546997625910860001675475 6820496438866290002513213)
                    ·
                      refine ⟨2557686164574858750942455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6820496438866290002513213 2557686164574858750942455)
                      ·
                        rfl

theorem cell23_4981076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 3, 1, 1, 3].length) (baseStart_4981076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4981076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4981076 prefixEnd_4981076 := by exact prefixLift 4981076
  have htrace : WordTrace (prefixWord ++ tailWord_4981076) baseStart_4981076 baseEnd_4981076 := by
    simpa [prefixWord, tailWord_4981076, baseEnd_4981076] using wordTrace_append hprefix tailTrace_4981076
  have hstable : (prefixWord ++ tailWord_4981076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4981076).length < 2 ^ (prefixWord ++ tailWord_4981076).sum := by decide
  have hdescent : baseEnd_4981076 < baseStart_4981076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4981076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4981109 : List Nat := [1, 3, 4, 1, 2, 1, 4, 1, 2, 4]
def baseStart_4981109 : Nat := 118140960795 + 4981109 * 2 ^ 59
def prefixEnd_4981109 : Nat := 4983230072969 + 3 ^ 40 * 4981109 * 2
def baseEnd_4981109 : Nat := 852567703145485707276601

theorem tailTrace_4981109 : CollatzResearch.WordTrace tailWord_4981109 prefixEnd_4981109 852567703145485707276601 := by
  unfold tailWord_4981109
  simp only [CollatzResearch.WordTrace]
  refine ⟨181675970511300273534170381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121117313674200182356113587 181675970511300273534170381)
  ·
    refine ⟨68128488941737602575313893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181675970511300273534170381 68128488941737602575313893)
    ·
      refine ⟨12774091676575800482871355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68128488941737602575313893 12774091676575800482871355)
      ·
        refine ⟨19161137514863700724307033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12774091676575800482871355 19161137514863700724307033)
        ·
          refine ⟨14370853136147775543230275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19161137514863700724307033 14370853136147775543230275)
          ·
            refine ⟨21556279704221663314845413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14370853136147775543230275 21556279704221663314845413)
            ·
              refine ⟨4041802444541561871533515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21556279704221663314845413 4041802444541561871533515)
              ·
                refine ⟨6062703666812342807300273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4041802444541561871533515 6062703666812342807300273)
                ·
                  refine ⟨4547027750109257105475205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6062703666812342807300273 4547027750109257105475205)
                  ·
                    refine ⟨852567703145485707276601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4547027750109257105475205 852567703145485707276601)
                    ·
                      rfl

theorem cell23_4981109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_4981109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4981109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4981109 prefixEnd_4981109 := by exact prefixLift 4981109
  have htrace : WordTrace (prefixWord ++ tailWord_4981109) baseStart_4981109 baseEnd_4981109 := by
    simpa [prefixWord, tailWord_4981109, baseEnd_4981109] using wordTrace_append hprefix tailTrace_4981109
  have hstable : (prefixWord ++ tailWord_4981109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4981109).length < 2 ^ (prefixWord ++ tailWord_4981109).sum := by decide
  have hdescent : baseEnd_4981109 < baseStart_4981109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4981109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4981150 : List Nat := [4, 3, 1, 2, 1, 1, 4, 2, 1, 2, 2]
def baseStart_4981150 : Nat := 118140960795 + 4981150 * 2 ^ 59
def prefixEnd_4981150 : Nat := 4983230072969 + 3 ^ 40 * 4981150 * 2
def baseEnd_4981150 : Nat := 2557724162143291461417115

theorem tailTrace_4981150 : CollatzResearch.WordTrace tailWord_4981150 prefixEnd_4981150 2557724162143291461417115 := by
  unfold tailWord_4981150
  simp only [CollatzResearch.WordTrace]
  refine ⟨22709683238018967192051613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121118310602767825024275269 22709683238018967192051613)
  ·
    refine ⟨8516131214257112697019355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22709683238018967192051613 8516131214257112697019355)
    ·
      refine ⟨12774196821385669045529033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8516131214257112697019355 12774196821385669045529033)
      ·
        refine ⟨9580647616039251784146775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12774196821385669045529033 9580647616039251784146775)
        ·
          refine ⟨14370971424058877676220163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9580647616039251784146775 14370971424058877676220163)
          ·
            refine ⟨21556457136088316514330245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14370971424058877676220163 21556457136088316514330245)
            ·
              refine ⟨4041835713016559346436921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21556457136088316514330245 4041835713016559346436921)
              ·
                refine ⟨3031376784762419509827691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4041835713016559346436921 3031376784762419509827691)
                ·
                  refine ⟨4547065177143629264741537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3031376784762419509827691 4547065177143629264741537)
                  ·
                    refine ⟨3410298882857721948556153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4547065177143629264741537 3410298882857721948556153)
                    ·
                      refine ⟨2557724162143291461417115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3410298882857721948556153 2557724162143291461417115)
                      ·
                        rfl

theorem cell23_4981150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_4981150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4981150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4981150 prefixEnd_4981150 := by exact prefixLift 4981150
  have htrace : WordTrace (prefixWord ++ tailWord_4981150) baseStart_4981150 baseEnd_4981150 := by
    simpa [prefixWord, tailWord_4981150, baseEnd_4981150] using wordTrace_append hprefix tailTrace_4981150
  have hstable : (prefixWord ++ tailWord_4981150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4981150).length < 2 ^ (prefixWord ++ tailWord_4981150).sum := by decide
  have hdescent : baseEnd_4981150 < baseStart_4981150 := by decide
  rcases family_descends (prefixWord ++ tailWord_4981150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4981206 : List Nat := [5, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2]
def baseStart_4981206 : Nat := 118140960795 + 4981206 * 2 ^ 59
def prefixEnd_4981206 : Nat := 4983230072969 + 3 ^ 40 * 4981206 * 2
def baseEnd_4981206 : Nat := 2557752917059943242316857

theorem tailTrace_4981206 : CollatzResearch.WordTrace tailWord_4981206 prefixEnd_4981206 2557752917059943242316857 := by
  unfold tailWord_4981206
  simp only [CollatzResearch.WordTrace]
  refine ⟨11354969274496803693778217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 121119672261299239400300981 11354969274496803693778217)
  ·
    refine ⟨8516226955872602770333663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11354969274496803693778217 8516226955872602770333663)
    ·
      refine ⟨12774340433808904155500495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8516226955872602770333663 12774340433808904155500495)
      ·
        refine ⟨19161510650713356233250743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12774340433808904155500495 19161510650713356233250743)
        ·
          refine ⟨28742265976070034349876115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19161510650713356233250743 28742265976070034349876115)
          ·
            refine ⟨43113398964105051524814173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28742265976070034349876115 43113398964105051524814173)
            ·
              refine ⟨16167524611539394321805315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43113398964105051524814173 16167524611539394321805315)
              ·
                refine ⟨24251286917309091482707973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16167524611539394321805315 24251286917309091482707973)
                ·
                  refine ⟨4547116296995454653007745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24251286917309091482707973 4547116296995454653007745)
                  ·
                    refine ⟨3410337222746590989755809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4547116296995454653007745 3410337222746590989755809)
                    ·
                      refine ⟨2557752917059943242316857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3410337222746590989755809 2557752917059943242316857)
                      ·
                        rfl

theorem cell23_4981206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_4981206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4981206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4981206 prefixEnd_4981206 := by exact prefixLift 4981206
  have htrace : WordTrace (prefixWord ++ tailWord_4981206) baseStart_4981206 baseEnd_4981206 := by
    simpa [prefixWord, tailWord_4981206, baseEnd_4981206] using wordTrace_append hprefix tailTrace_4981206
  have hstable : (prefixWord ++ tailWord_4981206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4981206).length < 2 ^ (prefixWord ++ tailWord_4981206).sum := by decide
  have hdescent : baseEnd_4981206 < baseStart_4981206 := by decide
  rcases family_descends (prefixWord ++ tailWord_4981206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4981245 : List Nat := [1, 4, 1, 1, 1, 3, 1, 3, 1, 3, 4]
def baseStart_4981245 : Nat := 118140960795 + 4981245 * 2 ^ 59
def prefixEnd_4981245 : Nat := 4983230072969 + 3 ^ 40 * 4981245 * 2
def baseEnd_4981245 : Nat := 2557772942805468589729177

theorem tailTrace_4981245 : CollatzResearch.WordTrace tailWord_4981245 prefixEnd_4981245 2557772942805468589729177 := by
  unfold tailWord_4981245
  simp only [CollatzResearch.WordTrace]
  refine ⟨181680930838807568761121189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121120620559205045840747459 181680930838807568761121189)
  ·
    refine ⟨34065174532276419142710223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 181680930838807568761121189 34065174532276419142710223)
    ·
      refine ⟨51097761798414628714065335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34065174532276419142710223 51097761798414628714065335)
      ·
        refine ⟨76646642697621943071098003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51097761798414628714065335 76646642697621943071098003)
        ·
          refine ⟨114969964046432914606647005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76646642697621943071098003 114969964046432914606647005)
          ·
            refine ⟨43113736517412342977492627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114969964046432914606647005 43113736517412342977492627)
            ·
              refine ⟨64670604776118514466238941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43113736517412342977492627 64670604776118514466238941)
              ·
                refine ⟨24251476791044442924839603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64670604776118514466238941 24251476791044442924839603)
                ·
                  refine ⟨36377215186566664387259405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24251476791044442924839603 36377215186566664387259405)
                  ·
                    refine ⟨13641455694962499145222277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36377215186566664387259405 13641455694962499145222277)
                    ·
                      refine ⟨2557772942805468589729177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13641455694962499145222277 2557772942805468589729177)
                      ·
                        rfl

theorem cell23_4981245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_4981245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4981245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4981245 prefixEnd_4981245 := by exact prefixLift 4981245
  have htrace : WordTrace (prefixWord ++ tailWord_4981245) baseStart_4981245 baseEnd_4981245 := by
    simpa [prefixWord, tailWord_4981245, baseEnd_4981245] using wordTrace_append hprefix tailTrace_4981245
  have hstable : (prefixWord ++ tailWord_4981245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4981245).length < 2 ^ (prefixWord ++ tailWord_4981245).sum := by decide
  have hdescent : baseEnd_4981245 < baseStart_4981245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4981245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4981262 : List Nat := [4, 1, 1, 2, 3, 1, 1, 1, 4, 1, 4]
def baseStart_4981262 : Nat := 118140960795 + 4981262 * 2 ^ 59
def prefixEnd_4981262 : Nat := 4983230072969 + 3 ^ 40 * 4981262 * 2
def baseEnd_4981262 : Nat := 2557781671976595023216599

theorem tailTrace_4981262 : CollatzResearch.WordTrace tailWord_4981262 prefixEnd_4981262 2557781671976595023216599 := by
  unfold tailWord_4981262
  simp only [CollatzResearch.WordTrace]
  refine ⟨22710193859968247583061255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121121033919830653776326693 22710193859968247583061255)
  ·
    refine ⟨34065290789952371374591883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22710193859968247583061255 34065290789952371374591883)
    ·
      refine ⟨51097936184928557061887825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34065290789952371374591883 51097936184928557061887825)
      ·
        refine ⟨38323452138696417796415869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51097936184928557061887825 38323452138696417796415869)
        ·
          refine ⟨14371294552011156673655951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38323452138696417796415869 14371294552011156673655951)
          ·
            refine ⟨21556941828016735010483927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14371294552011156673655951 21556941828016735010483927)
            ·
              refine ⟨32335412742025102515725891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21556941828016735010483927 32335412742025102515725891)
              ·
                refine ⟨48503119113037653773588837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32335412742025102515725891 48503119113037653773588837)
                ·
                  refine ⟨9094334833694560082547907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48503119113037653773588837 9094334833694560082547907)
                  ·
                    refine ⟨13641502250541840123821861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9094334833694560082547907 13641502250541840123821861)
                    ·
                      refine ⟨2557781671976595023216599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13641502250541840123821861 2557781671976595023216599)
                      ·
                        rfl

theorem cell23_4981262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_4981262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4981262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4981262 prefixEnd_4981262 := by exact prefixLift 4981262
  have htrace : WordTrace (prefixWord ++ tailWord_4981262) baseStart_4981262 baseEnd_4981262 := by
    simpa [prefixWord, tailWord_4981262, baseEnd_4981262] using wordTrace_append hprefix tailTrace_4981262
  have hstable : (prefixWord ++ tailWord_4981262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4981262).length < 2 ^ (prefixWord ++ tailWord_4981262).sum := by decide
  have hdescent : baseEnd_4981262 < baseStart_4981262 := by decide
  rcases family_descends (prefixWord ++ tailWord_4981262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4981265 : List Nat := [1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 3]
def baseStart_4981265 : Nat := 118140960795 + 4981265 * 2 ^ 59
def prefixEnd_4981265 : Nat := 4983230072969 + 3 ^ 40 * 4981265 * 2
def baseEnd_4981265 : Nat := 2557783212418558511479085

theorem tailTrace_4981265 : CollatzResearch.WordTrace tailWord_4981265 prefixEnd_4981265 2557783212418558511479085 := by
  unfold tailWord_4981265
  simp only [CollatzResearch.WordTrace]
  refine ⟨181681660298735112176849249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121121106865823408117899499 181681660298735112176849249)
  ·
    refine ⟨136261245224051334132636937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181681660298735112176849249 136261245224051334132636937)
    ·
      refine ⟨102195933918038500599477703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136261245224051334132636937 102195933918038500599477703)
      ·
        refine ⟨153293900877057750899216555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102195933918038500599477703 153293900877057750899216555)
        ·
          refine ⟨229940851315586626348824833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153293900877057750899216555 229940851315586626348824833)
          ·
            refine ⟨172455638486689969761618625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 229940851315586626348824833 172455638486689969761618625)
            ·
              refine ⟨129341728865017477321213969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 172455638486689969761618625 129341728865017477321213969)
              ·
                refine ⟨97006296648763107990910477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129341728865017477321213969 97006296648763107990910477)
                ·
                  refine ⟨36377361243286165496591429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97006296648763107990910477 36377361243286165496591429)
                  ·
                    refine ⟨6820755233116156030610893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36377361243286165496591429 6820755233116156030610893)
                    ·
                      refine ⟨2557783212418558511479085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6820755233116156030610893 2557783212418558511479085)
                      ·
                        rfl

theorem cell23_4981265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 3].length) (baseStart_4981265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4981265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4981265 prefixEnd_4981265 := by exact prefixLift 4981265
  have htrace : WordTrace (prefixWord ++ tailWord_4981265) baseStart_4981265 baseEnd_4981265 := by
    simpa [prefixWord, tailWord_4981265, baseEnd_4981265] using wordTrace_append hprefix tailTrace_4981265
  have hstable : (prefixWord ++ tailWord_4981265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4981265).length < 2 ^ (prefixWord ++ tailWord_4981265).sum := by decide
  have hdescent : baseEnd_4981265 < baseStart_4981265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4981265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4981282 : List Nat := [3, 3, 1, 1, 1, 1, 1, 1, 6, 2, 3]
def baseStart_4981282 : Nat := 118140960795 + 4981282 * 2 ^ 59
def prefixEnd_4981282 : Nat := 4983230072969 + 3 ^ 40 * 4981282 * 2
def baseEnd_4981282 : Nat := 2557791941589684944966507

theorem tailTrace_4981282 : CollatzResearch.WordTrace tailWord_4981282 prefixEnd_4981282 2557791941589684944966507 := by
  unfold tailWord_4981282
  simp only [CollatzResearch.WordTrace]
  refine ⟨45420570084918381020054525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121121520226449016053478733 45420570084918381020054525)
  ·
    refine ⟨17032713781844392882520447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45420570084918381020054525 17032713781844392882520447)
    ·
      refine ⟨25549070672766589323780671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17032713781844392882520447 25549070672766589323780671)
      ·
        refine ⟨38323606009149883985671007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25549070672766589323780671 38323606009149883985671007)
        ·
          refine ⟨57485409013724825978506511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38323606009149883985671007 57485409013724825978506511)
          ·
            refine ⟨86228113520587238967759767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57485409013724825978506511 86228113520587238967759767)
            ·
              refine ⟨129342170280880858451639651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86228113520587238967759767 129342170280880858451639651)
              ·
                refine ⟨194013255421321287677459477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129342170280880858451639651 194013255421321287677459477)
                ·
                  refine ⟨9094371347874435359880913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 194013255421321287677459477 9094371347874435359880913)
                  ·
                    refine ⟨6820778510905826519910685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9094371347874435359880913 6820778510905826519910685)
                    ·
                      refine ⟨2557791941589684944966507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6820778510905826519910685 2557791941589684944966507)
                      ·
                        rfl

theorem cell23_4981282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_4981282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4981282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4981282 prefixEnd_4981282 := by exact prefixLift 4981282
  have htrace : WordTrace (prefixWord ++ tailWord_4981282) baseStart_4981282 baseEnd_4981282 := by
    simpa [prefixWord, tailWord_4981282, baseEnd_4981282] using wordTrace_append hprefix tailTrace_4981282
  have hstable : (prefixWord ++ tailWord_4981282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4981282).length < 2 ^ (prefixWord ++ tailWord_4981282).sum := by decide
  have hdescent : baseEnd_4981282 < baseStart_4981282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4981282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4981293 : List Nat := [1, 5, 4, 1, 1, 1, 2, 1, 2, 5]
def baseStart_4981293 : Nat := 118140960795 + 4981293 * 2 ^ 59
def prefixEnd_4981293 : Nat := 4983230072969 + 3 ^ 40 * 4981293 * 2
def baseEnd_4981293 : Nat := 852599196625628133976319

theorem tailTrace_4981293 : CollatzResearch.WordTrace tailWord_4981293 prefixEnd_4981293 852599196625628133976319 := by
  unfold tailWord_4981293
  simp only [CollatzResearch.WordTrace]
  refine ⟨181682681542633672958868533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121121787695089115305912355 181682681542633672958868533)
  ·
    refine ⟨17032751394621906839893925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 181682681542633672958868533 17032751394621906839893925)
    ·
      refine ⟨3193640886491607532480111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17032751394621906839893925 3193640886491607532480111)
      ·
        refine ⟨4790461329737411298720167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3193640886491607532480111 4790461329737411298720167)
        ·
          refine ⟨7185691994606116948080251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4790461329737411298720167 7185691994606116948080251)
          ·
            refine ⟨10778537991909175422120377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7185691994606116948080251 10778537991909175422120377)
            ·
              refine ⟨8083903493931881566590283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10778537991909175422120377 8083903493931881566590283)
              ·
                refine ⟨12125855240897822349885425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8083903493931881566590283 12125855240897822349885425)
                ·
                  refine ⟨9094391430673366762414069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12125855240897822349885425 9094391430673366762414069)
                  ·
                    refine ⟨852599196625628133976319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9094391430673366762414069 852599196625628133976319)
                    ·
                      rfl

theorem cell23_4981293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_4981293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4981293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4981293 prefixEnd_4981293 := by exact prefixLift 4981293
  have htrace : WordTrace (prefixWord ++ tailWord_4981293) baseStart_4981293 baseEnd_4981293 := by
    simpa [prefixWord, tailWord_4981293, baseEnd_4981293] using wordTrace_append hprefix tailTrace_4981293
  have hstable : (prefixWord ++ tailWord_4981293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4981293).length < 2 ^ (prefixWord ++ tailWord_4981293).sum := by decide
  have hdescent : baseEnd_4981293 < baseStart_4981293 := by decide
  rcases family_descends (prefixWord ++ tailWord_4981293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4981332 : List Nat := [2, 4, 1, 1, 1, 3, 1, 2, 3, 5]
def baseStart_4981332 : Nat := 118140960795 + 4981332 * 2 ^ 59
def prefixEnd_4981332 : Nat := 4983230072969 + 3 ^ 40 * 4981332 * 2
def baseEnd_4981332 : Nat := 852605871874136583113759

theorem tailTrace_4981332 : CollatzResearch.WordTrace tailWord_4981332 prefixEnd_4981332 852605871874136583113759 := by
  unfold tailWord_4981332
  simp only [CollatzResearch.WordTrace]
  refine ⟨90842051994746191309769125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121122735992994921746358833 90842051994746191309769125)
  ·
    refine ⟨17032884749014910870581711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90842051994746191309769125 17032884749014910870581711)
    ·
      refine ⟨25549327123522366305872567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17032884749014910870581711 25549327123522366305872567)
      ·
        refine ⟨38323990685283549458808851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25549327123522366305872567 38323990685283549458808851)
        ·
          refine ⟨57485986027925324188213277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38323990685283549458808851 57485986027925324188213277)
          ·
            refine ⟨21557244760471996570579979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57485986027925324188213277 21557244760471996570579979)
            ·
              refine ⟨32335867140707994855869969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21557244760471996570579979 32335867140707994855869969)
              ·
                refine ⟨24251900355530996141902477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32335867140707994855869969 24251900355530996141902477)
                ·
                  refine ⟨9094462633324123553213429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24251900355530996141902477 9094462633324123553213429)
                  ·
                    refine ⟨852605871874136583113759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9094462633324123553213429 852605871874136583113759)
                    ·
                      rfl

theorem cell23_4981332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_4981332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4981332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4981332 prefixEnd_4981332 := by exact prefixLift 4981332
  have htrace : WordTrace (prefixWord ++ tailWord_4981332) baseStart_4981332 baseEnd_4981332 := by
    simpa [prefixWord, tailWord_4981332, baseEnd_4981332] using wordTrace_append hprefix tailTrace_4981332
  have hstable : (prefixWord ++ tailWord_4981332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4981332).length < 2 ^ (prefixWord ++ tailWord_4981332).sum := by decide
  have hdescent : baseEnd_4981332 < baseStart_4981332 := by decide
  rcases family_descends (prefixWord ++ tailWord_4981332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4981355 : List Nat := [1, 1, 1, 1, 2, 2, 1, 3, 5, 1, 5]
def baseStart_4981355 : Nat := 118140960795 + 4981355 * 2 ^ 59
def prefixEnd_4981355 : Nat := 4983230072969 + 3 ^ 40 * 4981355 * 2
def baseEnd_4981355 : Nat := 2557829425677463159353671

theorem tailTrace_4981355 : CollatzResearch.WordTrace tailWord_4981355 prefixEnd_4981355 2557829425677463159353671 := by
  unfold tailWord_4981355
  simp only [CollatzResearch.WordTrace]
  refine ⟨181684942868409057547625519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121123295245606038365083679 181684942868409057547625519)
  ·
    refine ⟨272527414302613586321438279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181684942868409057547625519 272527414302613586321438279)
    ·
      refine ⟨408791121453920379482157419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272527414302613586321438279 408791121453920379482157419)
      ·
        refine ⟨613186682180880569223236129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 408791121453920379482157419 613186682180880569223236129)
        ·
          refine ⟨459890011635660426917427097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 613186682180880569223236129 459890011635660426917427097)
          ·
            refine ⟨344917508726745320188070323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 459890011635660426917427097 344917508726745320188070323)
            ·
              refine ⟨517376263090117980282105485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 344917508726745320188070323 517376263090117980282105485)
              ·
                refine ⟨194016098658794242605789557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 517376263090117980282105485 194016098658794242605789557)
                ·
                  refine ⟨18189009249261960244292771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 194016098658794242605789557 18189009249261960244292771)
                  ·
                    refine ⟨27283513873892940366439157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18189009249261960244292771 27283513873892940366439157)
                    ·
                      refine ⟨2557829425677463159353671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27283513873892940366439157 2557829425677463159353671)
                      ·
                        rfl

theorem cell23_4981355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5, 1, 5].length) (baseStart_4981355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4981355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4981355 prefixEnd_4981355 := by exact prefixLift 4981355
  have htrace : WordTrace (prefixWord ++ tailWord_4981355) baseStart_4981355 baseEnd_4981355 := by
    simpa [prefixWord, tailWord_4981355, baseEnd_4981355] using wordTrace_append hprefix tailTrace_4981355
  have hstable : (prefixWord ++ tailWord_4981355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4981355).length < 2 ^ (prefixWord ++ tailWord_4981355).sum := by decide
  have hdescent : baseEnd_4981355 < baseStart_4981355 := by decide
  rcases family_descends (prefixWord ++ tailWord_4981355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4981366 : List Nat := [5, 1, 1, 2, 3, 1, 1, 3, 1, 5]
def baseStart_4981366 : Nat := 118140960795 + 4981366 * 2 ^ 59
def prefixEnd_4981366 : Nat := 4983230072969 + 3 ^ 40 * 4981366 * 2
def baseEnd_4981366 : Nat := 852611691321554205438707

theorem tailTrace_4981366 : CollatzResearch.WordTrace tailWord_4981366 prefixEnd_4981366 852611691321554205438707 := by
  unfold tailWord_4981366
  simp only [CollatzResearch.WordTrace]
  refine ⟨11355334004460575401642247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 121123562714246137617517301 11355334004460575401642247)
  ·
    refine ⟨17033001006690863102463371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11355334004460575401642247 17033001006690863102463371)
    ·
      refine ⟨25549501510036294653695057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17033001006690863102463371 25549501510036294653695057)
      ·
        refine ⟨19162126132527220990271293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25549501510036294653695057 19162126132527220990271293)
        ·
          refine ⟨7185797299697707871351735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19162126132527220990271293 7185797299697707871351735)
          ·
            refine ⟨10778695949546561807027603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7185797299697707871351735 10778695949546561807027603)
            ·
              refine ⟨16168043924319842710541405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10778695949546561807027603 16168043924319842710541405)
              ·
                refine ⟨6063016471619941016453027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16168043924319842710541405 6063016471619941016453027)
                ·
                  refine ⟨9094524707429911524679541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6063016471619941016453027 9094524707429911524679541)
                  ·
                    refine ⟨852611691321554205438707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9094524707429911524679541 852611691321554205438707)
                    ·
                      rfl

theorem cell23_4981366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_4981366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4981366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4981366 prefixEnd_4981366 := by exact prefixLift 4981366
  have htrace : WordTrace (prefixWord ++ tailWord_4981366) baseStart_4981366 baseEnd_4981366 := by
    simpa [prefixWord, tailWord_4981366, baseEnd_4981366] using wordTrace_append hprefix tailTrace_4981366
  have hstable : (prefixWord ++ tailWord_4981366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4981366).length < 2 ^ (prefixWord ++ tailWord_4981366).sum := by decide
  have hdescent : baseEnd_4981366 < baseStart_4981366 := by decide
  rcases family_descends (prefixWord ++ tailWord_4981366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4981369 : List Nat := [1, 2, 1, 3, 3, 3, 1, 3, 1, 1, 4]
def baseStart_4981369 : Nat := 118140960795 + 4981369 * 2 ^ 59
def prefixEnd_4981369 : Nat := 4983230072969 + 3 ^ 40 * 4981369 * 2
def baseEnd_4981369 : Nat := 2557836614406626104578607

theorem tailTrace_4981369 : CollatzResearch.WordTrace tailWord_4981369 prefixEnd_4981369 2557836614406626104578607 := by
  unfold tailWord_4981369
  simp only [CollatzResearch.WordTrace]
  refine ⟨181685453490358337938635161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121123635660238891959090107 181685453490358337938635161)
  ·
    refine ⟨136264090117768753453976371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181685453490358337938635161 136264090117768753453976371)
    ·
      refine ⟨204396135176653130180964557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136264090117768753453976371 204396135176653130180964557)
      ·
        refine ⟨76648550691244923817861709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 204396135176653130180964557 76648550691244923817861709)
        ·
          refine ⟨28743206509216846431698141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76648550691244923817861709 28743206509216846431698141)
          ·
            refine ⟨10778702440956317411886803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28743206509216846431698141 10778702440956317411886803)
            ·
              refine ⟨16168053661434476117830205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10778702440956317411886803 16168053661434476117830205)
              ·
                refine ⟨6063020123037928544186327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16168053661434476117830205 6063020123037928544186327)
                ·
                  refine ⟨9094530184556892816279491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6063020123037928544186327 9094530184556892816279491)
                  ·
                    refine ⟨13641795276835339224419237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9094530184556892816279491 13641795276835339224419237)
                    ·
                      refine ⟨2557836614406626104578607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13641795276835339224419237 2557836614406626104578607)
                      ·
                        rfl

theorem cell23_4981369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 3, 1, 1, 4].length) (baseStart_4981369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4981369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4981369 prefixEnd_4981369 := by exact prefixLift 4981369
  have htrace : WordTrace (prefixWord ++ tailWord_4981369) baseStart_4981369 baseEnd_4981369 := by
    simpa [prefixWord, tailWord_4981369, baseEnd_4981369] using wordTrace_append hprefix tailTrace_4981369
  have hstable : (prefixWord ++ tailWord_4981369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4981369).length < 2 ^ (prefixWord ++ tailWord_4981369).sum := by decide
  have hdescent : baseEnd_4981369 < baseStart_4981369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4981369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4981379 : List Nat := [1, 1, 1, 3, 3, 1, 5, 2, 2, 4]
def baseStart_4981379 : Nat := 118140960795 + 4981379 * 2 ^ 59
def prefixEnd_4981379 : Nat := 4983230072969 + 3 ^ 40 * 4981379 * 2
def baseEnd_4981379 : Nat := 852613916404390355151187

theorem tailTrace_4981379 : CollatzResearch.WordTrace tailWord_4981379 prefixEnd_4981379 852613916404390355151187 := by
  unfold tailWord_4981379
  simp only [CollatzResearch.WordTrace]
  refine ⟨181685818220322109646499191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121123878813548073097666127 181685818220322109646499191)
  ·
    refine ⟨272528727330483164469748787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181685818220322109646499191 272528727330483164469748787)
    ·
      refine ⟨408793090995724746704623181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272528727330483164469748787 408793090995724746704623181)
      ·
        refine ⟨153297409123396780014233693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 408793090995724746704623181 153297409123396780014233693)
        ·
          refine ⟨57486528421273792505337635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153297409123396780014233693 57486528421273792505337635)
          ·
            refine ⟨86229792631910688758006453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57486528421273792505337635 86229792631910688758006453)
            ·
              refine ⟨8084043059241627071063105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 86229792631910688758006453 8084043059241627071063105)
              ·
                refine ⟨6063032294431220303297329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8084043059241627071063105 6063032294431220303297329)
                ·
                  refine ⟨4547274220823415227472997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6063032294431220303297329 4547274220823415227472997)
                  ·
                    refine ⟨852613916404390355151187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4547274220823415227472997 852613916404390355151187)
                    ·
                      rfl

theorem cell23_4981379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 2, 2, 4].length) (baseStart_4981379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4981379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4981379 prefixEnd_4981379 := by exact prefixLift 4981379
  have htrace : WordTrace (prefixWord ++ tailWord_4981379) baseStart_4981379 baseEnd_4981379 := by
    simpa [prefixWord, tailWord_4981379, baseEnd_4981379] using wordTrace_append hprefix tailTrace_4981379
  have hstable : (prefixWord ++ tailWord_4981379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4981379).length < 2 ^ (prefixWord ++ tailWord_4981379).sum := by decide
  have hdescent : baseEnd_4981379 < baseStart_4981379 := by decide
  rcases family_descends (prefixWord ++ tailWord_4981379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4981385 : List Nat := [1, 2, 1, 1, 4, 1, 1, 1, 2, 2, 7]
def baseStart_4981385 : Nat := 118140960795 + 4981385 * 2 ^ 59
def prefixEnd_4981385 : Nat := 4983230072969 + 3 ^ 40 * 4981385 * 2
def baseEnd_4981385 : Nat := 2557844830097098041978533

theorem tailTrace_4981385 : CollatzResearch.WordTrace tailWord_4981385 prefixEnd_4981385 2557844830097098041978533 := by
  unfold tailWord_4981385
  simp only [CollatzResearch.WordTrace]
  refine ⟨181686037058300372671217609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121124024705533581780811739 181686037058300372671217609)
  ·
    refine ⟨136264527793725279503413207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181686037058300372671217609 136264527793725279503413207)
    ·
      refine ⟨204396791690587919255119811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136264527793725279503413207 204396791690587919255119811)
      ·
        refine ⟨306595187535881878882679717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204396791690587919255119811 306595187535881878882679717)
        ·
          refine ⟨57486597662977852290502447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 306595187535881878882679717 57486597662977852290502447)
          ·
            refine ⟨86229896494466778435753671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57486597662977852290502447 86229896494466778435753671)
            ·
              refine ⟨129344844741700167653630507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86229896494466778435753671 129344844741700167653630507)
              ·
                refine ⟨194017267112550251480445761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129344844741700167653630507 194017267112550251480445761)
                ·
                  refine ⟨145512950334412688610334321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 194017267112550251480445761 145512950334412688610334321)
                  ·
                    refine ⟨109134712750809516457750741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 145512950334412688610334321 109134712750809516457750741)
                    ·
                      refine ⟨2557844830097098041978533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 109134712750809516457750741 2557844830097098041978533)
                      ·
                        rfl

theorem cell23_4981385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 2, 7].length) (baseStart_4981385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4981385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4981385 prefixEnd_4981385 := by exact prefixLift 4981385
  have htrace : WordTrace (prefixWord ++ tailWord_4981385) baseStart_4981385 baseEnd_4981385 := by
    simpa [prefixWord, tailWord_4981385, baseEnd_4981385] using wordTrace_append hprefix tailTrace_4981385
  have hstable : (prefixWord ++ tailWord_4981385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4981385).length < 2 ^ (prefixWord ++ tailWord_4981385).sum := by decide
  have hdescent : baseEnd_4981385 < baseStart_4981385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4981385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4981395 : List Nat := [1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 6]
def baseStart_4981395 : Nat := 118140960795 + 4981395 * 2 ^ 59
def prefixEnd_4981395 : Nat := 4983230072969 + 3 ^ 40 * 4981395 * 2
def baseEnd_4981395 : Nat := 2557849964903643002853487

theorem tailTrace_4981395 : CollatzResearch.WordTrace tailWord_4981395 prefixEnd_4981395 2557849964903643002853487 := by
  unfold tailWord_4981395
  simp only [CollatzResearch.WordTrace]
  refine ⟨181686401788264144379081639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121124267858842762919387759 181686401788264144379081639)
  ·
    refine ⟨272529602682396216568622459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181686401788264144379081639 272529602682396216568622459)
    ·
      refine ⟨408794404023594324852933689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272529602682396216568622459 408794404023594324852933689)
      ·
        refine ⟨306595803017695743639700267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 408794404023594324852933689 306595803017695743639700267)
        ·
          refine ⟨459893704526543615459550401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 306595803017695743639700267 459893704526543615459550401)
          ·
            refine ⟨344920278394907711594662801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 459893704526543615459550401 344920278394907711594662801)
            ·
              refine ⟨258690208796180783695997101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 344920278394907711594662801 258690208796180783695997101)
              ·
                refine ⟨97008828298567793885998913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 258690208796180783695997101 97008828298567793885998913)
                ·
                  refine ⟨72756621223925845414499185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97008828298567793885998913 72756621223925845414499185)
                  ·
                    refine ⟨54567465917944384060874389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 72756621223925845414499185 54567465917944384060874389)
                    ·
                      refine ⟨2557849964903643002853487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54567465917944384060874389 2557849964903643002853487)
                      ·
                        rfl

theorem cell23_4981395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 6].length) (baseStart_4981395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4981395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4981395 prefixEnd_4981395 := by exact prefixLift 4981395
  have htrace : WordTrace (prefixWord ++ tailWord_4981395) baseStart_4981395 baseEnd_4981395 := by
    simpa [prefixWord, tailWord_4981395, baseEnd_4981395] using wordTrace_append hprefix tailTrace_4981395
  have hstable : (prefixWord ++ tailWord_4981395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4981395).length < 2 ^ (prefixWord ++ tailWord_4981395).sum := by decide
  have hdescent : baseEnd_4981395 < baseStart_4981395 := by decide
  rcases family_descends (prefixWord ++ tailWord_4981395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4981396 : List Nat := [2, 4, 2, 2, 1, 3, 1, 1, 1, 6]
def baseStart_4981396 : Nat := 118140960795 + 4981396 * 2 ^ 59
def prefixEnd_4981396 : Nat := 4983230072969 + 3 ^ 40 * 4981396 * 2
def baseEnd_4981396 : Nat := 852616826128099166313661

theorem tailTrace_4981396 : CollatzResearch.WordTrace tailWord_4981396 prefixEnd_4981396 852616826128099166313661 := by
  unfold tailWord_4981396
  simp only [CollatzResearch.WordTrace]
  refine ⟨90843219130630260774934021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121124292174173681033245361 90843219130630260774934021)
  ·
    refine ⟨17033103586993173895300129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90843219130630260774934021 17033103586993173895300129)
    ·
      refine ⟨12774827690244880421475097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17033103586993173895300129 12774827690244880421475097)
      ·
        refine ⟨9581120767683660316106323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12774827690244880421475097 9581120767683660316106323)
        ·
          refine ⟨14371681151525490474159485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9581120767683660316106323 14371681151525490474159485)
          ·
            refine ⟨5389380431822058927809807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14371681151525490474159485 5389380431822058927809807)
            ·
              refine ⟨8084070647733088391714711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5389380431822058927809807 8084070647733088391714711)
              ·
                refine ⟨12126105971599632587572067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8084070647733088391714711 12126105971599632587572067)
                ·
                  refine ⟨18189158957399448881358101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12126105971599632587572067 18189158957399448881358101)
                  ·
                    refine ⟨852616826128099166313661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18189158957399448881358101 852616826128099166313661)
                    ·
                      rfl

theorem cell23_4981396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_4981396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4981396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4981396 prefixEnd_4981396 := by exact prefixLift 4981396
  have htrace : WordTrace (prefixWord ++ tailWord_4981396) baseStart_4981396 baseEnd_4981396 := by
    simpa [prefixWord, tailWord_4981396, baseEnd_4981396] using wordTrace_append hprefix tailTrace_4981396
  have hstable : (prefixWord ++ tailWord_4981396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4981396).length < 2 ^ (prefixWord ++ tailWord_4981396).sum := by decide
  have hdescent : baseEnd_4981396 < baseStart_4981396 := by decide
  rcases family_descends (prefixWord ++ tailWord_4981396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4981436 : List Nat := [2, 2, 2, 3, 1, 1, 2, 4, 2, 1, 3]
def baseStart_4981436 : Nat := 118140960795 + 4981436 * 2 ^ 59
def prefixEnd_4981436 : Nat := 4983230072969 + 3 ^ 40 * 4981436 * 2
def baseEnd_4981436 : Nat := 2557871017610477342440799

theorem tailTrace_4981436 : CollatzResearch.WordTrace tailWord_4981436 prefixEnd_4981436 2557871017610477342440799 := by
  unfold tailWord_4981436
  simp only [CollatzResearch.WordTrace]
  refine ⟨90843948590557804190662081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121125264787410405587549441 90843948590557804190662081)
  ·
    refine ⟨68132961442918353142996561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90843948590557804190662081 68132961442918353142996561)
    ·
      refine ⟨51099721082188764857247421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68132961442918353142996561 51099721082188764857247421)
      ·
        refine ⟨19162395405820786821467783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51099721082188764857247421 19162395405820786821467783)
        ·
          refine ⟨28743593108731180232201675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19162395405820786821467783 28743593108731180232201675)
          ·
            refine ⟨43115389663096770348302513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28743593108731180232201675 43115389663096770348302513)
            ·
              refine ⟨32336542247322577761226885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43115389663096770348302513 32336542247322577761226885)
              ·
                refine ⟨6063101671372983330230041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32336542247322577761226885 6063101671372983330230041)
                ·
                  refine ⟨4547326253529737497672531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6063101671372983330230041 4547326253529737497672531)
                  ·
                    refine ⟨6820989380294606246508797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4547326253529737497672531 6820989380294606246508797)
                    ·
                      refine ⟨2557871017610477342440799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6820989380294606246508797 2557871017610477342440799)
                      ·
                        rfl

theorem cell23_4981436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_4981436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4981436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4981436 prefixEnd_4981436 := by exact prefixLift 4981436
  have htrace : WordTrace (prefixWord ++ tailWord_4981436) baseStart_4981436 baseEnd_4981436 := by
    simpa [prefixWord, tailWord_4981436, baseEnd_4981436] using wordTrace_append hprefix tailTrace_4981436
  have hstable : (prefixWord ++ tailWord_4981436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4981436).length < 2 ^ (prefixWord ++ tailWord_4981436).sum := by decide
  have hdescent : baseEnd_4981436 < baseStart_4981436 := by decide
  rcases family_descends (prefixWord ++ tailWord_4981436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4981463 : List Nat := [1, 1, 3, 2, 1, 6, 1, 2, 1, 3, 2]
def baseStart_4981463 : Nat := 118140960795 + 4981463 * 2 ^ 59
def prefixEnd_4981463 : Nat := 4983230072969 + 3 ^ 40 * 4981463 * 2
def baseEnd_4981463 : Nat := 2557884881588148736803175

theorem tailTrace_4981463 : CollatzResearch.WordTrace tailWord_4981463 prefixEnd_4981463 2557884881588148736803175 := by
  unfold tailWord_4981463
  simp only [CollatzResearch.WordTrace]
  refine ⟨181688881952017791992557043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121125921301345194661704695 181688881952017791992557043)
  ·
    refine ⟨272533322928026687988835565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181688881952017791992557043 272533322928026687988835565)
    ·
      refine ⟨102199996098010007995813337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 272533322928026687988835565 102199996098010007995813337)
      ·
        refine ⟨76649997073507505996860003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102199996098010007995813337 76649997073507505996860003)
        ·
          refine ⟨114974995610261258995290005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76649997073507505996860003 114974995610261258995290005)
          ·
            refine ⟨5389452919230996515404219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 114974995610261258995290005 5389452919230996515404219)
            ·
              refine ⟨8084179378846494773106329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5389452919230996515404219 8084179378846494773106329)
              ·
                refine ⟨6063134534134871079829747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8084179378846494773106329 6063134534134871079829747)
                ·
                  refine ⟨9094701801202306619744621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6063134534134871079829747 9094701801202306619744621)
                  ·
                    refine ⟨3410513175450864982404233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9094701801202306619744621 3410513175450864982404233)
                    ·
                      refine ⟨2557884881588148736803175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3410513175450864982404233 2557884881588148736803175)
                      ·
                        rfl

theorem cell23_4981463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 2, 1, 3, 2].length) (baseStart_4981463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4981463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4981463 prefixEnd_4981463 := by exact prefixLift 4981463
  have htrace : WordTrace (prefixWord ++ tailWord_4981463) baseStart_4981463 baseEnd_4981463 := by
    simpa [prefixWord, tailWord_4981463, baseEnd_4981463] using wordTrace_append hprefix tailTrace_4981463
  have hstable : (prefixWord ++ tailWord_4981463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4981463).length < 2 ^ (prefixWord ++ tailWord_4981463).sum := by decide
  have hdescent : baseEnd_4981463 < baseStart_4981463 := by decide
  rcases family_descends (prefixWord ++ tailWord_4981463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4981472 : List Nat := [2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 4]
def baseStart_4981472 : Nat := 118140960795 + 4981472 * 2 ^ 59
def prefixEnd_4981472 : Nat := 4983230072969 + 3 ^ 40 * 4981472 * 2
def baseEnd_4981472 : Nat := 2557889502914039201590633

theorem tailTrace_4981472 : CollatzResearch.WordTrace tailWord_4981472 prefixEnd_4981472 2557889502914039201590633 := by
  unfold tailWord_4981472
  simp only [CollatzResearch.WordTrace]
  refine ⟨90844605104492593264817335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121126140139323457686423113 90844605104492593264817335)
  ·
    refine ⟨136266907656738889897226003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90844605104492593264817335 136266907656738889897226003)
    ·
      refine ⟨204400361485108334845839005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136266907656738889897226003 204400361485108334845839005)
      ·
        refine ⟨76650135556915625567189627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 204400361485108334845839005 76650135556915625567189627)
        ·
          refine ⟨114975203335373438350784441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76650135556915625567189627 114975203335373438350784441)
          ·
            refine ⟨86231402501530078763088331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114975203335373438350784441 86231402501530078763088331)
            ·
              refine ⟨129347103752295118144632497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86231402501530078763088331 129347103752295118144632497)
              ·
                refine ⟨97010327814221338608474373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129347103752295118144632497 97010327814221338608474373)
                ·
                  refine ⟨18189436465166500989088945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 97010327814221338608474373 18189436465166500989088945)
                  ·
                    refine ⟨13642077348874875741816709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18189436465166500989088945 13642077348874875741816709)
                    ·
                      refine ⟨2557889502914039201590633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13642077348874875741816709 2557889502914039201590633)
                      ·
                        rfl

theorem cell23_4981472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_4981472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4981472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4981472 prefixEnd_4981472 := by exact prefixLift 4981472
  have htrace : WordTrace (prefixWord ++ tailWord_4981472) baseStart_4981472 baseEnd_4981472 := by
    simpa [prefixWord, tailWord_4981472, baseEnd_4981472] using wordTrace_append hprefix tailTrace_4981472
  have hstable : (prefixWord ++ tailWord_4981472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4981472).length < 2 ^ (prefixWord ++ tailWord_4981472).sum := by decide
  have hdescent : baseEnd_4981472 < baseStart_4981472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4981472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4981476 : List Nat := [2, 3, 1, 1, 1, 5, 1, 2, 1, 4, 2]
def baseStart_4981476 : Nat := 118140960795 + 4981476 * 2 ^ 59
def prefixEnd_4981476 : Nat := 4983230072969 + 3 ^ 40 * 4981476 * 2
def baseEnd_4981476 : Nat := 2557891556836657185940615

theorem tailTrace_4981476 : CollatzResearch.WordTrace tailWord_4981476 prefixEnd_4981476 2557891556836657185940615 := by
  unfold tailWord_4981476
  simp only [CollatzResearch.WordTrace]
  refine ⟨90844678050485347606390141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121126237400647130141853521 90844678050485347606390141)
  ·
    refine ⟨34066754268932005352396303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90844678050485347606390141 34066754268932005352396303)
    ·
      refine ⟨51100131403398008028594455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34066754268932005352396303 51100131403398008028594455)
      ·
        refine ⟨76650197105097012042891683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51100131403398008028594455 76650197105097012042891683)
        ·
          refine ⟨114975295657645518064337525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76650197105097012042891683 114975295657645518064337525)
          ·
            refine ⟨10778933967904267318531643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 114975295657645518064337525 10778933967904267318531643)
            ·
              refine ⟨16168400951856400977797465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10778933967904267318531643 16168400951856400977797465)
              ·
                refine ⟨12126300713892300733348099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16168400951856400977797465 12126300713892300733348099)
                ·
                  refine ⟨18189451070838451100022149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12126300713892300733348099 18189451070838451100022149)
                  ·
                    refine ⟨3410522075782209581254153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18189451070838451100022149 3410522075782209581254153)
                    ·
                      refine ⟨2557891556836657185940615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3410522075782209581254153 2557891556836657185940615)
                      ·
                        rfl

theorem cell23_4981476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 2, 1, 4, 2].length) (baseStart_4981476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4981476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4981476 prefixEnd_4981476 := by exact prefixLift 4981476
  have htrace : WordTrace (prefixWord ++ tailWord_4981476) baseStart_4981476 baseEnd_4981476 := by
    simpa [prefixWord, tailWord_4981476, baseEnd_4981476] using wordTrace_append hprefix tailTrace_4981476
  have hstable : (prefixWord ++ tailWord_4981476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4981476).length < 2 ^ (prefixWord ++ tailWord_4981476).sum := by decide
  have hdescent : baseEnd_4981476 < baseStart_4981476 := by decide
  rcases family_descends (prefixWord ++ tailWord_4981476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4981480 : List Nat := [2, 1, 4, 1, 4, 1, 3, 1, 1, 3, 2]
def baseStart_4981480 : Nat := 118140960795 + 4981480 * 2 ^ 59
def prefixEnd_4981480 : Nat := 4983230072969 + 3 ^ 40 * 4981480 * 2
def baseEnd_4981480 : Nat := 2557893610759275170290597

theorem tailTrace_4981480 : CollatzResearch.WordTrace tailWord_4981480 prefixEnd_4981480 2557893610759275170290597 := by
  unfold tailWord_4981480
  simp only [CollatzResearch.WordTrace]
  refine ⟨90844750996478101947962947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121126334661970802597283929 90844750996478101947962947)
  ·
    refine ⟨136267126494717152921944421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90844750996478101947962947 136267126494717152921944421)
    ·
      refine ⟨25550086217759466172864579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 136267126494717152921944421 25550086217759466172864579)
      ·
        refine ⟨38325129326639199259296869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25550086217759466172864579 38325129326639199259296869)
        ·
          refine ⟨7185961748744849861118163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38325129326639199259296869 7185961748744849861118163)
          ·
            refine ⟨10778942623117274791677245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7185961748744849861118163 10778942623117274791677245)
            ·
              refine ⟨4042103483668978046878967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10778942623117274791677245 4042103483668978046878967)
              ·
                refine ⟨6063155225503467070318451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4042103483668978046878967 6063155225503467070318451)
                ·
                  refine ⟨9094732838255200605477677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6063155225503467070318451 9094732838255200605477677)
                  ·
                    refine ⟨3410524814345700227054129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9094732838255200605477677 3410524814345700227054129)
                    ·
                      refine ⟨2557893610759275170290597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3410524814345700227054129 2557893610759275170290597)
                      ·
                        rfl

theorem cell23_4981480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 1, 1, 3, 2].length) (baseStart_4981480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4981480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4981480 prefixEnd_4981480 := by exact prefixLift 4981480
  have htrace : WordTrace (prefixWord ++ tailWord_4981480) baseStart_4981480 baseEnd_4981480 := by
    simpa [prefixWord, tailWord_4981480, baseEnd_4981480] using wordTrace_append hprefix tailTrace_4981480
  have hstable : (prefixWord ++ tailWord_4981480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4981480).length < 2 ^ (prefixWord ++ tailWord_4981480).sum := by decide
  have hdescent : baseEnd_4981480 < baseStart_4981480 := by decide
  rcases family_descends (prefixWord ++ tailWord_4981480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4981506 : List Nat := [3, 4, 1, 1, 1, 3, 1, 1, 2, 2, 4]
def baseStart_4981506 : Nat := 118140960795 + 4981506 * 2 ^ 59
def prefixEnd_4981506 : Nat := 4983230072969 + 3 ^ 40 * 4981506 * 2
def baseEnd_4981506 : Nat := 2557906961256292068565477

theorem tailTrace_4981506 : CollatzResearch.WordTrace tailWord_4981506 prefixEnd_4981506 2557906961256292068565477 := by
  unfold tailWord_4981506
  simp only [CollatzResearch.WordTrace]
  refine ⟨45422612572715502584093093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121126966860574673557581581 45422612572715502584093093)
  ·
    refine ⟨8516739857384156734517455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45422612572715502584093093 8516739857384156734517455)
    ·
      refine ⟨12775109786076235101776183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8516739857384156734517455 12775109786076235101776183)
      ·
        refine ⟨19162664679114352652664275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12775109786076235101776183 19162664679114352652664275)
        ·
          refine ⟨28743997018671528978996413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19162664679114352652664275 28743997018671528978996413)
          ·
            refine ⟨10778998882001823367123655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28743997018671528978996413 10778998882001823367123655)
            ·
              refine ⟨16168498323002735050685483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10778998882001823367123655 16168498323002735050685483)
              ·
                refine ⟨24252747484504102576028225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16168498323002735050685483 24252747484504102576028225)
                ·
                  refine ⟨18189560613378076932021169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24252747484504102576028225 18189560613378076932021169)
                  ·
                    refine ⟨13642170460033557699015877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18189560613378076932021169 13642170460033557699015877)
                    ·
                      refine ⟨2557906961256292068565477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13642170460033557699015877 2557906961256292068565477)
                      ·
                        rfl

theorem cell23_4981506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_4981506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4981506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4981506 prefixEnd_4981506 := by exact prefixLift 4981506
  have htrace : WordTrace (prefixWord ++ tailWord_4981506) baseStart_4981506 baseEnd_4981506 := by
    simpa [prefixWord, tailWord_4981506, baseEnd_4981506] using wordTrace_append hprefix tailTrace_4981506
  have hstable : (prefixWord ++ tailWord_4981506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4981506).length < 2 ^ (prefixWord ++ tailWord_4981506).sum := by decide
  have hdescent : baseEnd_4981506 < baseStart_4981506 := by decide
  rcases family_descends (prefixWord ++ tailWord_4981506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4981519 : List Nat := [1, 1, 2, 1, 1, 1, 5, 2, 2, 5, 2]
def baseStart_4981519 : Nat := 118140960795 + 4981519 * 2 ^ 59
def prefixEnd_4981519 : Nat := 4983230072969 + 3 ^ 40 * 4981519 * 2
def baseEnd_4981519 : Nat := 2557913636504800517702917

theorem tailTrace_4981519 : CollatzResearch.WordTrace tailWord_4981519 prefixEnd_4981519 2557913636504800517702917 := by
  unfold tailWord_4981519
  simp only [CollatzResearch.WordTrace]
  refine ⟨181690924439814913556595611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121127282959876609037730407 181690924439814913556595611)
  ·
    refine ⟨272536386659722370334893417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181690924439814913556595611 272536386659722370334893417)
    ·
      refine ⟨204402289994791777751170063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 272536386659722370334893417 204402289994791777751170063)
      ·
        refine ⟨306603434992187666626755095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204402289994791777751170063 306603434992187666626755095)
        ·
          refine ⟨459905152488281499940132643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 306603434992187666626755095 459905152488281499940132643)
          ·
            refine ⟨689857728732422249910198965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 459905152488281499940132643 689857728732422249910198965)
            ·
              refine ⟨64674162068664585929081153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 689857728732422249910198965 64674162068664585929081153)
              ·
                refine ⟨48505621551498439446810865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64674162068664585929081153 48505621551498439446810865)
                ·
                  refine ⟨36379216163623829585108149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48505621551498439446810865 36379216163623829585108149)
                  ·
                    refine ⟨3410551515339734023603889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36379216163623829585108149 3410551515339734023603889)
                    ·
                      refine ⟨2557913636504800517702917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3410551515339734023603889 2557913636504800517702917)
                      ·
                        rfl

theorem cell23_4981519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 5, 2].length) (baseStart_4981519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4981519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4981519 prefixEnd_4981519 := by exact prefixLift 4981519
  have htrace : WordTrace (prefixWord ++ tailWord_4981519) baseStart_4981519 baseEnd_4981519 := by
    simpa [prefixWord, tailWord_4981519, baseEnd_4981519] using wordTrace_append hprefix tailTrace_4981519
  have hstable : (prefixWord ++ tailWord_4981519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4981519).length < 2 ^ (prefixWord ++ tailWord_4981519).sum := by decide
  have hdescent : baseEnd_4981519 < baseStart_4981519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4981519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4981552 : List Nat := [2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 5]
def baseStart_4981552 : Nat := 118140960795 + 4981552 * 2 ^ 59
def prefixEnd_4981552 : Nat := 4983230072969 + 3 ^ 40 * 4981552 * 2
def baseEnd_4981552 : Nat := 2557930581366398888590265

theorem tailTrace_4981552 : CollatzResearch.WordTrace tailWord_4981552 prefixEnd_4981552 2557930581366398888590265 := by
  unfold tailWord_4981552
  simp only [CollatzResearch.WordTrace]
  refine ⟨90846064024347680096273455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121128085365796906795031273 90846064024347680096273455)
  ·
    refine ⟨136269096036521520144410183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90846064024347680096273455 136269096036521520144410183)
    ·
      refine ⟨204403644054782280216615275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136269096036521520144410183 204403644054782280216615275)
      ·
        refine ⟨306605466082173420324922913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204403644054782280216615275 306605466082173420324922913)
        ·
          refine ⟨229954099561630065243692185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 306605466082173420324922913 229954099561630065243692185)
          ·
            refine ⟨172465574671222548932769139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 229954099561630065243692185 172465574671222548932769139)
            ·
              refine ⟨258698362006833823399153709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172465574671222548932769139 258698362006833823399153709)
              ·
                refine ⟨97011885752562683774682641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 258698362006833823399153709 97011885752562683774682641)
                ·
                  refine ⟨72758914314422012831011981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97011885752562683774682641 72758914314422012831011981)
                  ·
                    refine ⟨27284592867908254811629493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 72758914314422012831011981 27284592867908254811629493)
                    ·
                      refine ⟨2557930581366398888590265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27284592867908254811629493 2557930581366398888590265)
                      ·
                        rfl

theorem cell23_4981552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 5].length) (baseStart_4981552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4981552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4981552 prefixEnd_4981552 := by exact prefixLift 4981552
  have htrace : WordTrace (prefixWord ++ tailWord_4981552) baseStart_4981552 baseEnd_4981552 := by
    simpa [prefixWord, tailWord_4981552, baseEnd_4981552] using wordTrace_append hprefix tailTrace_4981552
  have hstable : (prefixWord ++ tailWord_4981552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4981552).length < 2 ^ (prefixWord ++ tailWord_4981552).sum := by decide
  have hdescent : baseEnd_4981552 < baseStart_4981552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4981552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4981586 : List Nat := [3, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3]
def baseStart_4981586 : Nat := 118140960795 + 4981586 * 2 ^ 59
def prefixEnd_4981586 : Nat := 4983230072969 + 3 ^ 40 * 4981586 * 2
def baseEnd_4981586 : Nat := 2557948039708651755565109

theorem tailTrace_4981586 : CollatzResearch.WordTrace tailWord_4981586 prefixEnd_4981586 2557948039708651755565109 := by
  unfold tailWord_4981586
  simp only [CollatzResearch.WordTrace]
  refine ⟨45423342032643045999821153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121128912087048122666189741 45423342032643045999821153)
  ·
    refine ⟨34067506524482284499865865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45423342032643045999821153 34067506524482284499865865)
    ·
      refine ⟨25550629893361713374899399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34067506524482284499865865 25550629893361713374899399)
      ·
        refine ⟨38325944840042570062349099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25550629893361713374899399 38325944840042570062349099)
        ·
          refine ⟨57488917260063855093523649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38325944840042570062349099 57488917260063855093523649)
          ·
            refine ⟨43116687945047891320142737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57488917260063855093523649 43116687945047891320142737)
            ·
              refine ⟨32337515958785918490107053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43116687945047891320142737 32337515958785918490107053)
              ·
                refine ⟨12126568484544719433790145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32337515958785918490107053 12126568484544719433790145)
                ·
                  refine ⟨9094926363408539575342609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12126568484544719433790145 9094926363408539575342609)
                  ·
                    refine ⟨6821194772556404681506957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9094926363408539575342609 6821194772556404681506957)
                    ·
                      refine ⟨2557948039708651755565109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6821194772556404681506957 2557948039708651755565109)
                      ·
                        rfl

theorem cell23_4981586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_4981586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4981586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4981586 prefixEnd_4981586 := by exact prefixLift 4981586
  have htrace : WordTrace (prefixWord ++ tailWord_4981586) baseStart_4981586 baseEnd_4981586 := by
    simpa [prefixWord, tailWord_4981586, baseEnd_4981586] using wordTrace_append hprefix tailTrace_4981586
  have hstable : (prefixWord ++ tailWord_4981586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4981586).length < 2 ^ (prefixWord ++ tailWord_4981586).sum := by decide
  have hdescent : baseEnd_4981586 < baseStart_4981586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4981586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4981593 : List Nat := [1, 2, 1, 2, 2, 4, 3, 3, 1, 4]
def baseStart_4981593 : Nat := 118140960795 + 4981593 * 2 ^ 59
def prefixEnd_4981593 : Nat := 4983230072969 + 3 ^ 40 * 4981593 * 2
def baseEnd_4981593 : Nat := 852650544691077742725859

theorem tailTrace_4981593 : CollatzResearch.WordTrace tailWord_4981593 prefixEnd_4981593 852650544691077742725859 := by
  unfold tailWord_4981593
  simp only [CollatzResearch.WordTrace]
  refine ⟨181693623441546824194789433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121129082294364549463192955 181693623441546824194789433)
  ·
    refine ⟨136270217581160118146092075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181693623441546824194789433 136270217581160118146092075)
    ·
      refine ⟨204405326371740177219138113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136270217581160118146092075 204405326371740177219138113)
      ·
        refine ⟨153303994778805132914353585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204405326371740177219138113 153303994778805132914353585)
        ·
          refine ⟨114977996084103849685765189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153303994778805132914353585 114977996084103849685765189)
          ·
            refine ⟨21558374265769471816080973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 114977996084103849685765189 21558374265769471816080973)
            ·
              refine ⟨8084390349663551931030365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21558374265769471816080973 8084390349663551931030365)
              ·
                refine ⟨3031646381123831974136387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8084390349663551931030365 3031646381123831974136387)
                ·
                  refine ⟨4547469571685747961204581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3031646381123831974136387 4547469571685747961204581)
                  ·
                    refine ⟨852650544691077742725859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4547469571685747961204581 852650544691077742725859)
                    ·
                      rfl

theorem cell23_4981593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 3, 1, 4].length) (baseStart_4981593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4981593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4981593 prefixEnd_4981593 := by exact prefixLift 4981593
  have htrace : WordTrace (prefixWord ++ tailWord_4981593) baseStart_4981593 baseEnd_4981593 := by
    simpa [prefixWord, tailWord_4981593, baseEnd_4981593] using wordTrace_append hprefix tailTrace_4981593
  have hstable : (prefixWord ++ tailWord_4981593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4981593).length < 2 ^ (prefixWord ++ tailWord_4981593).sum := by decide
  have hdescent : baseEnd_4981593 < baseStart_4981593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4981593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4981626 : List Nat := [3, 1, 1, 1, 1, 1, 3, 1, 6, 3, 2]
def baseStart_4981626 : Nat := 118140960795 + 4981626 * 2 ^ 59
def prefixEnd_4981626 : Nat := 4983230072969 + 3 ^ 40 * 4981626 * 2
def baseEnd_4981626 : Nat := 2557968578934831599064925

theorem tailTrace_4981626 : CollatzResearch.WordTrace tailWord_4981626 prefixEnd_4981626 2557968578934831599064925 := by
  unfold tailWord_4981626
  simp only [CollatzResearch.WordTrace]
  refine ⟨45423706762606817707685183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121129884700284847220493821 45423706762606817707685183)
  ·
    refine ⟨68135560143910226561527775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45423706762606817707685183 68135560143910226561527775)
    ·
      refine ⟨102203340215865339842291663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68135560143910226561527775 102203340215865339842291663)
      ·
        refine ⟨153305010323798009763437495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102203340215865339842291663 153305010323798009763437495)
        ·
          refine ⟨229957515485697014645156243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153305010323798009763437495 229957515485697014645156243)
          ·
            refine ⟨344936273228545521967734365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229957515485697014645156243 344936273228545521967734365)
            ·
              refine ⟨129351102460704570737900387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 344936273228545521967734365 129351102460704570737900387)
              ·
                refine ⟨194026653691056856106850581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129351102460704570737900387 194026653691056856106850581)
                ·
                  refine ⟨9094999391768290130008621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 194026653691056856106850581 9094999391768290130008621)
                  ·
                    refine ⟨3410624771913108798753233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9094999391768290130008621 3410624771913108798753233)
                    ·
                      refine ⟨2557968578934831599064925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3410624771913108798753233 2557968578934831599064925)
                      ·
                        rfl

theorem cell23_4981626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 6, 3, 2].length) (baseStart_4981626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4981626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4981626 prefixEnd_4981626 := by exact prefixLift 4981626
  have htrace : WordTrace (prefixWord ++ tailWord_4981626) baseStart_4981626 baseEnd_4981626 := by
    simpa [prefixWord, tailWord_4981626, baseEnd_4981626] using wordTrace_append hprefix tailTrace_4981626
  have hstable : (prefixWord ++ tailWord_4981626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4981626).length < 2 ^ (prefixWord ++ tailWord_4981626).sum := by decide
  have hdescent : baseEnd_4981626 < baseStart_4981626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4981626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4981653 : List Nat := [1, 3, 2, 1, 1, 5, 3, 1, 1, 5]
def baseStart_4981653 : Nat := 118140960795 + 4981653 * 2 ^ 59
def prefixEnd_4981653 : Nat := 4983230072969 + 3 ^ 40 * 4981653 * 2
def baseEnd_4981653 : Nat := 852660814304167664475767

theorem tailTrace_4981653 : CollatzResearch.WordTrace tailWord_4981653 prefixEnd_4981653 852660814304167664475767 := by
  unfold tailWord_4981653
  simp only [CollatzResearch.WordTrace]
  refine ⟨181695811821329454441973613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121130541214219636294649075 181695811821329454441973613)
  ·
    refine ⟨68135929432998545415740105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181695811821329454441973613 68135929432998545415740105)
    ·
      refine ⟨51101947074748909061805079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68135929432998545415740105 51101947074748909061805079)
      ·
        refine ⟨76652920612123363592707619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51101947074748909061805079 76652920612123363592707619)
        ·
          refine ⟨114979380918185045389061429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76652920612123363592707619 114979380918185045389061429)
          ·
            refine ⟨10779316961079848005224509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 114979380918185045389061429 10779316961079848005224509)
            ·
              refine ⟨4042243860404943001959191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10779316961079848005224509 4042243860404943001959191)
              ·
                refine ⟨6063365790607414502938787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4042243860404943001959191 6063365790607414502938787)
                ·
                  refine ⟨9095048685911121754408181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6063365790607414502938787 9095048685911121754408181)
                  ·
                    refine ⟨852660814304167664475767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9095048685911121754408181 852660814304167664475767)
                    ·
                      rfl

theorem cell23_4981653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 1, 1, 5].length) (baseStart_4981653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4981653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4981653 prefixEnd_4981653 := by exact prefixLift 4981653
  have htrace : WordTrace (prefixWord ++ tailWord_4981653) baseStart_4981653 baseEnd_4981653 := by
    simpa [prefixWord, tailWord_4981653, baseEnd_4981653] using wordTrace_append hprefix tailTrace_4981653
  have hstable : (prefixWord ++ tailWord_4981653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4981653).length < 2 ^ (prefixWord ++ tailWord_4981653).sum := by decide
  have hdescent : baseEnd_4981653 < baseStart_4981653 := by decide
  rcases family_descends (prefixWord ++ tailWord_4981653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4981673 : List Nat := [1, 2, 1, 1, 1, 1, 6, 3, 3, 2, 2]
def baseStart_4981673 : Nat := 118140960795 + 4981673 * 2 ^ 59
def prefixEnd_4981673 : Nat := 4983230072969 + 3 ^ 40 * 4981673 * 2
def baseEnd_4981673 : Nat := 2557992712525592915177209

theorem tailTrace_4981673 : CollatzResearch.WordTrace tailWord_4981673 prefixEnd_4981673 2557992712525592915177209 := by
  unfold tailWord_4981673
  simp only [CollatzResearch.WordTrace]
  refine ⟨181696541281256997857701673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121131027520837998571801115 181696541281256997857701673)
  ·
    refine ⟨136272405960942748393276255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181696541281256997857701673 136272405960942748393276255)
    ·
      refine ⟨204408608941414122589914383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136272405960942748393276255 204408608941414122589914383)
      ·
        refine ⟨306612913412121183884871575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204408608941414122589914383 306612913412121183884871575)
        ·
          refine ⟨459919370118181775827307363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 306612913412121183884871575 459919370118181775827307363)
          ·
            refine ⟨689879055177272663740961045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 459919370118181775827307363 689879055177272663740961045)
            ·
              refine ⟨32338080711434656112857549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 689879055177272663740961045 32338080711434656112857549)
              ·
                refine ⟨12126780266787996042321581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32338080711434656112857549 12126780266787996042321581)
                ·
                  refine ⟨4547542600045498515870593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12126780266787996042321581 4547542600045498515870593)
                  ·
                    refine ⟨3410656950034123886902945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4547542600045498515870593 3410656950034123886902945)
                    ·
                      refine ⟨2557992712525592915177209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3410656950034123886902945 2557992712525592915177209)
                      ·
                        rfl

theorem cell23_4981673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3, 3, 2, 2].length) (baseStart_4981673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4981673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4981673 prefixEnd_4981673 := by exact prefixLift 4981673
  have htrace : WordTrace (prefixWord ++ tailWord_4981673) baseStart_4981673 baseEnd_4981673 := by
    simpa [prefixWord, tailWord_4981673, baseEnd_4981673] using wordTrace_append hprefix tailTrace_4981673
  have hstable : (prefixWord ++ tailWord_4981673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4981673).length < 2 ^ (prefixWord ++ tailWord_4981673).sum := by decide
  have hdescent : baseEnd_4981673 < baseStart_4981673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4981673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4981696 : List Nat := [2, 1, 1, 2, 3, 4, 3, 7]
def baseStart_4981696 : Nat := 118140960795 + 4981696 * 2 ^ 59
def prefixEnd_4981696 : Nat := 4983230072969 + 3 ^ 40 * 4981696 * 2
def baseEnd_4981696 : Nat := 94740908243727641673689

theorem tailTrace_4981696 : CollatzResearch.WordTrace tailWord_4981696 prefixEnd_4981696 94740908243727641673689 := by
  unfold tailWord_4981696
  simp only [CollatzResearch.WordTrace]
  refine ⟨90848690080086836392894471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121131586773449115190525961 90848690080086836392894471)
  ·
    refine ⟨136273035120130254589341707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90848690080086836392894471 136273035120130254589341707)
    ·
      refine ⟨204409552680195381884012561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136273035120130254589341707 204409552680195381884012561)
      ·
        refine ⟨153307164510146536413009421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204409552680195381884012561 153307164510146536413009421)
        ·
          refine ⟨57490186691304951154878533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153307164510146536413009421 57490186691304951154878533)
          ·
            refine ⟨10779410004619678341539725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57490186691304951154878533 10779410004619678341539725)
            ·
              refine ⟨4042278751732379378077397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10779410004619678341539725 4042278751732379378077397)
              ·
                refine ⟨94740908243727641673689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4042278751732379378077397 94740908243727641673689)
                ·
                  rfl

theorem cell23_4981696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 7].length) (baseStart_4981696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4981696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4981696 prefixEnd_4981696 := by exact prefixLift 4981696
  have htrace : WordTrace (prefixWord ++ tailWord_4981696) baseStart_4981696 baseEnd_4981696 := by
    simpa [prefixWord, tailWord_4981696, baseEnd_4981696] using wordTrace_append hprefix tailTrace_4981696
  have hstable : (prefixWord ++ tailWord_4981696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4981696).length < 2 ^ (prefixWord ++ tailWord_4981696).sum := by decide
  have hdescent : baseEnd_4981696 < baseStart_4981696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4981696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4981707 : List Nat := [1, 1, 1, 1, 3, 6, 2, 3, 1, 2, 2]
def baseStart_4981707 : Nat := 118140960795 + 4981707 * 2 ^ 59
def prefixEnd_4981707 : Nat := 4983230072969 + 3 ^ 40 * 4981707 * 2
def baseEnd_4981707 : Nat := 2558010170867845782152053

theorem tailTrace_4981707 : CollatzResearch.WordTrace tailWord_4981707 prefixEnd_4981707 2558010170867845782152053 := by
  unfold tailWord_4981707
  simp only [CollatzResearch.WordTrace]
  refine ⟨181697781363133821664439375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121131854242089214442959583 181697781363133821664439375)
  ·
    refine ⟨272546672044700732496659063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181697781363133821664439375 272546672044700732496659063)
    ·
      refine ⟨408820008067051098744988595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272546672044700732496659063 408820008067051098744988595)
      ·
        refine ⟨613230012100576648117482893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 408820008067051098744988595 613230012100576648117482893)
        ·
          refine ⟨229961254537716243044056085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 613230012100576648117482893 229961254537716243044056085)
          ·
            refine ⟨10779433806455448892690129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 229961254537716243044056085 10779433806455448892690129)
            ·
              refine ⟨8084575354841586669517597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10779433806455448892690129 8084575354841586669517597)
              ·
                refine ⟨3031715758065595001069099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8084575354841586669517597 3031715758065595001069099)
                ·
                  refine ⟨4547573637098392501603649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3031715758065595001069099 4547573637098392501603649)
                  ·
                    refine ⟨3410680227823794376202737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4547573637098392501603649 3410680227823794376202737)
                    ·
                      refine ⟨2558010170867845782152053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3410680227823794376202737 2558010170867845782152053)
                      ·
                        rfl

theorem cell23_4981707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 3, 1, 2, 2].length) (baseStart_4981707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4981707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4981707 prefixEnd_4981707 := by exact prefixLift 4981707
  have htrace : WordTrace (prefixWord ++ tailWord_4981707) baseStart_4981707 baseEnd_4981707 := by
    simpa [prefixWord, tailWord_4981707, baseEnd_4981707] using wordTrace_append hprefix tailTrace_4981707
  have hstable : (prefixWord ++ tailWord_4981707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4981707).length < 2 ^ (prefixWord ++ tailWord_4981707).sum := by decide
  have hdescent : baseEnd_4981707 < baseStart_4981707 := by decide
  rcases family_descends (prefixWord ++ tailWord_4981707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4981710 : List Nat := [4, 1, 1, 1, 2, 3, 4, 1, 1, 2, 3]
def baseStart_4981710 : Nat := 118140960795 + 4981710 * 2 ^ 59
def prefixEnd_4981710 : Nat := 4983230072969 + 3 ^ 40 * 4981710 * 2
def baseEnd_4981710 : Nat := 2558011711309809270414539

theorem tailTrace_4981710 : CollatzResearch.WordTrace tailWord_4981710 prefixEnd_4981710 2558011711309809270414539 := by
  unfold tailWord_4981710
  simp only [CollatzResearch.WordTrace]
  refine ⟨22712236347765369147099823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121131927188081968784532389 22712236347765369147099823)
  ·
    refine ⟨34068354521648053720649735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22712236347765369147099823 34068354521648053720649735)
    ·
      refine ⟨51102531782472080580974603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34068354521648053720649735 51102531782472080580974603)
      ·
        refine ⟨76653797673708120871461905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51102531782472080580974603 76653797673708120871461905)
        ·
          refine ⟨57490348255281090653596429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76653797673708120871461905 57490348255281090653596429)
          ·
            refine ⟨21558880595730408995098661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57490348255281090653596429 21558880595730408995098661)
            ·
              refine ⟨4042290111699451686580999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21558880595730408995098661 4042290111699451686580999)
              ·
                refine ⟨6063435167549177529871499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4042290111699451686580999 6063435167549177529871499)
                ·
                  refine ⟨9095152751323766294807249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6063435167549177529871499 9095152751323766294807249)
                  ·
                    refine ⟨6821364563492824721105437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9095152751323766294807249 6821364563492824721105437)
                    ·
                      refine ⟨2558011711309809270414539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6821364563492824721105437 2558011711309809270414539)
                      ·
                        rfl

theorem cell23_4981710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 1, 1, 2, 3].length) (baseStart_4981710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4981710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4981710 prefixEnd_4981710 := by exact prefixLift 4981710
  have htrace : WordTrace (prefixWord ++ tailWord_4981710) baseStart_4981710 baseEnd_4981710 := by
    simpa [prefixWord, tailWord_4981710, baseEnd_4981710] using wordTrace_append hprefix tailTrace_4981710
  have hstable : (prefixWord ++ tailWord_4981710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4981710).length < 2 ^ (prefixWord ++ tailWord_4981710).sum := by decide
  have hdescent : baseEnd_4981710 < baseStart_4981710 := by decide
  rcases family_descends (prefixWord ++ tailWord_4981710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4981717 : List Nat := [1, 3, 2, 3, 4, 1, 1, 2, 2, 4]
def baseStart_4981717 : Nat := 118140960795 + 4981717 * 2 ^ 59
def prefixEnd_4981717 : Nat := 4983230072969 + 3 ^ 40 * 4981717 * 2
def baseEnd_4981717 : Nat := 852671768558130247675669

theorem tailTrace_4981717 : CollatzResearch.WordTrace tailWord_4981717 prefixEnd_4981717 852671768558130247675669 := by
  unfold tailWord_4981717
  simp only [CollatzResearch.WordTrace]
  refine ⟨181698146093097593372303405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121132097395398395581535603 181698146093097593372303405)
  ·
    refine ⟨68136804784911597514613777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181698146093097593372303405 68136804784911597514613777)
    ·
      refine ⟨51102603588683698135960333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68136804784911597514613777 51102603588683698135960333)
      ·
        refine ⟨19163476345756386800985125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51102603588683698135960333 19163476345756386800985125)
        ·
          refine ⟨3593151814829322525184711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19163476345756386800985125 3593151814829322525184711)
          ·
            refine ⟨5389727722243983787777067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3593151814829322525184711 5389727722243983787777067)
            ·
              refine ⟨8084591583365975681665601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5389727722243983787777067 8084591583365975681665601)
              ·
                refine ⟨6063443687524481761249201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8084591583365975681665601 6063443687524481761249201)
                ·
                  refine ⟨4547582765643361320936901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6063443687524481761249201 4547582765643361320936901)
                  ·
                    refine ⟨852671768558130247675669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4547582765643361320936901 852671768558130247675669)
                    ·
                      rfl

theorem cell23_4981717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 2, 2, 4].length) (baseStart_4981717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4981717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4981717 prefixEnd_4981717 := by exact prefixLift 4981717
  have htrace : WordTrace (prefixWord ++ tailWord_4981717) baseStart_4981717 baseEnd_4981717 := by
    simpa [prefixWord, tailWord_4981717, baseEnd_4981717] using wordTrace_append hprefix tailTrace_4981717
  have hstable : (prefixWord ++ tailWord_4981717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4981717).length < 2 ^ (prefixWord ++ tailWord_4981717).sum := by decide
  have hdescent : baseEnd_4981717 < baseStart_4981717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4981717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4981719 : List Nat := [1, 1, 3, 2, 1, 1, 2, 1, 4, 2, 5]
def baseStart_4981719 : Nat := 118140960795 + 4981719 * 2 ^ 59
def prefixEnd_4981719 : Nat := 4983230072969 + 3 ^ 40 * 4981719 * 2
def baseEnd_4981719 : Nat := 2558016332635699735201997

theorem tailTrace_4981719 : CollatzResearch.WordTrace tailWord_4981719 prefixEnd_4981719 2558016332635699735201997 := by
  unfold tailWord_4981719
  simp only [CollatzResearch.WordTrace]
  refine ⟨181698219039090347713876211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121132146026060231809250807 181698219039090347713876211)
  ·
    refine ⟨272547328558635521570814317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181698219039090347713876211 272547328558635521570814317)
    ·
      refine ⟨102205248209488320589055369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 272547328558635521570814317 102205248209488320589055369)
      ·
        refine ⟨76653936157116240441791527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102205248209488320589055369 76653936157116240441791527)
        ·
          refine ⟨114980904235674360662687291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76653936157116240441791527 114980904235674360662687291)
          ·
            refine ⟨172471356353511540994030937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114980904235674360662687291 172471356353511540994030937)
            ·
              refine ⟨129353517265133655745523203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 172471356353511540994030937 129353517265133655745523203)
              ·
                refine ⟨194030275897700483618284805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129353517265133655745523203 194030275897700483618284805)
                ·
                  refine ⟨36380676730818840678428401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 194030275897700483618284805 36380676730818840678428401)
                  ·
                    refine ⟨27285507548114130508821301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36380676730818840678428401 27285507548114130508821301)
                    ·
                      refine ⟨2558016332635699735201997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27285507548114130508821301 2558016332635699735201997)
                      ·
                        rfl

theorem cell23_4981719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_4981719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4981719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4981719 prefixEnd_4981719 := by exact prefixLift 4981719
  have htrace : WordTrace (prefixWord ++ tailWord_4981719) baseStart_4981719 baseEnd_4981719 := by
    simpa [prefixWord, tailWord_4981719, baseEnd_4981719] using wordTrace_append hprefix tailTrace_4981719
  have hstable : (prefixWord ++ tailWord_4981719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4981719).length < 2 ^ (prefixWord ++ tailWord_4981719).sum := by decide
  have hdescent : baseEnd_4981719 < baseStart_4981719 := by decide
  rcases family_descends (prefixWord ++ tailWord_4981719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4981758 : List Nat := [4, 2, 2, 2, 3, 1, 1, 3, 1, 2, 2]
def baseStart_4981758 : Nat := 118140960795 + 4981758 * 2 ^ 59
def prefixEnd_4981758 : Nat := 4983230072969 + 3 ^ 40 * 4981758 * 2
def baseEnd_4981758 : Nat := 2558036358381225082614319

theorem tailTrace_4981758 : CollatzResearch.WordTrace tailWord_4981758 prefixEnd_4981758 2558036358381225082614319 := by
  unfold tailWord_4981758
  simp only [CollatzResearch.WordTrace]
  refine ⟨22712455185743632171818241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121133094323966038249697285 22712455185743632171818241)
  ·
    refine ⟨17034341389307724128863681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22712455185743632171818241 17034341389307724128863681)
    ·
      refine ⟨12775756041980793096647761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17034341389307724128863681 12775756041980793096647761)
      ·
        refine ⟨9581817031485594822485821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12775756041980793096647761 9581817031485594822485821)
        ·
          refine ⟨3593181386807098058432183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9581817031485594822485821 3593181386807098058432183)
          ·
            refine ⟨5389772080210647087648275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3593181386807098058432183 5389772080210647087648275)
            ·
              refine ⟨8084658120315970631472413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5389772080210647087648275 8084658120315970631472413)
              ·
                refine ⟨3031746795118488986802155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8084658120315970631472413 3031746795118488986802155)
                ·
                  refine ⟨4547620192677733480203233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3031746795118488986802155 4547620192677733480203233)
                  ·
                    refine ⟨3410715144508300110152425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4547620192677733480203233 3410715144508300110152425)
                    ·
                      refine ⟨2558036358381225082614319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3410715144508300110152425 2558036358381225082614319)
                      ·
                        rfl

theorem cell23_4981758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_4981758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4981758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4981758 prefixEnd_4981758 := by exact prefixLift 4981758
  have htrace : WordTrace (prefixWord ++ tailWord_4981758) baseStart_4981758 baseEnd_4981758 := by
    simpa [prefixWord, tailWord_4981758, baseEnd_4981758] using wordTrace_append hprefix tailTrace_4981758
  have hstable : (prefixWord ++ tailWord_4981758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4981758).length < 2 ^ (prefixWord ++ tailWord_4981758).sum := by decide
  have hdescent : baseEnd_4981758 < baseStart_4981758 := by decide
  rcases family_descends (prefixWord ++ tailWord_4981758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4981769 : List Nat := [1, 2, 1, 1, 3, 1, 1, 4, 9]
def baseStart_4981769 : Nat := 118140960795 + 4981769 * 2 ^ 59
def prefixEnd_4981769 : Nat := 4983230072969 + 3 ^ 40 * 4981769 * 2
def baseEnd_4981769 : Nat := 284226889629824948841863

theorem tailTrace_4981769 : CollatzResearch.WordTrace tailWord_4981769 prefixEnd_4981769 284226889629824948841863 := by
  unfold tailWord_4981769
  simp only [CollatzResearch.WordTrace]
  refine ⟨181700042688909206253196361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121133361792606137502130907 181700042688909206253196361)
  ·
    refine ⟨136275032016681904689897271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181700042688909206253196361 136275032016681904689897271)
    ·
      refine ⟨204412548025022857034845907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136275032016681904689897271 204412548025022857034845907)
      ·
        refine ⟨306618822037534285552268861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204412548025022857034845907 306618822037534285552268861)
        ·
          refine ⟨114982058264075357082100823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 306618822037534285552268861 114982058264075357082100823)
          ·
            refine ⟨172473087396113035623151235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114982058264075357082100823 172473087396113035623151235)
            ·
              refine ⟨258709631094169553434726853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172473087396113035623151235 258709631094169553434726853)
              ·
                refine ⟨48508055830156791269011285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 258709631094169553434726853 48508055830156791269011285)
                ·
                  refine ⟨284226889629824948841863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 48508055830156791269011285 284226889629824948841863)
                  ·
                    rfl

theorem cell23_4981769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 9].length) (baseStart_4981769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4981769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4981769 prefixEnd_4981769 := by exact prefixLift 4981769
  have htrace : WordTrace (prefixWord ++ tailWord_4981769) baseStart_4981769 baseEnd_4981769 := by
    simpa [prefixWord, tailWord_4981769, baseEnd_4981769] using wordTrace_append hprefix tailTrace_4981769
  have hstable : (prefixWord ++ tailWord_4981769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4981769).length < 2 ^ (prefixWord ++ tailWord_4981769).sum := by decide
  have hdescent : baseEnd_4981769 < baseStart_4981769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4981769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4981779 : List Nat := [1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 9]
def baseStart_4981779 : Nat := 118140960795 + 4981779 * 2 ^ 59
def prefixEnd_4981779 : Nat := 4983230072969 + 3 ^ 40 * 4981779 * 2
def baseEnd_4981779 : Nat := 2558047141474969500451721

theorem tailTrace_4981779 : CollatzResearch.WordTrace tailWord_4981779 prefixEnd_4981779 2558047141474969500451721 := by
  unfold tailWord_4981779
  simp only [CollatzResearch.WordTrace]
  refine ⟨181700407418872977961060391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121133604945915318640706927 181700407418872977961060391)
  ·
    refine ⟨272550611128309466941590587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181700407418872977961060391 272550611128309466941590587)
    ·
      refine ⟨408825916692464200412385881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272550611128309466941590587 408825916692464200412385881)
      ·
        refine ⟨306619437519348150309289411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 408825916692464200412385881 306619437519348150309289411)
        ·
          refine ⟨459929156279022225463934117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 306619437519348150309289411 459929156279022225463934117)
          ·
            refine ⟨86236716802316667274487647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 459929156279022225463934117 86236716802316667274487647)
            ·
              refine ⟨129355075203475000911731471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86236716802316667274487647 129355075203475000911731471)
              ·
                refine ⟨194032612805212501367597207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129355075203475000911731471 194032612805212501367597207)
                ·
                  refine ⟨291048919207818752051395811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 194032612805212501367597207 291048919207818752051395811)
                  ·
                    refine ⟨436573378811728128077093717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 291048919207818752051395811 436573378811728128077093717)
                    ·
                      refine ⟨2558047141474969500451721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 436573378811728128077093717 2558047141474969500451721)
                      ·
                        rfl

theorem cell23_4981779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 9].length) (baseStart_4981779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4981779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4981779 prefixEnd_4981779 := by exact prefixLift 4981779
  have htrace : WordTrace (prefixWord ++ tailWord_4981779) baseStart_4981779 baseEnd_4981779 := by
    simpa [prefixWord, tailWord_4981779, baseEnd_4981779] using wordTrace_append hprefix tailTrace_4981779
  have hstable : (prefixWord ++ tailWord_4981779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4981779).length < 2 ^ (prefixWord ++ tailWord_4981779).sum := by decide
  have hdescent : baseEnd_4981779 < baseStart_4981779 := by decide
  rcases family_descends (prefixWord ++ tailWord_4981779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4981836 : List Nat := [2, 2, 1, 3, 1, 1, 1, 2, 3, 3, 4]
def baseStart_4981836 : Nat := 118140960795 + 4981836 * 2 ^ 59
def prefixEnd_4981836 : Nat := 4983230072969 + 3 ^ 40 * 4981836 * 2
def baseEnd_4981836 : Nat := 2558076409872275777438959

theorem tailTrace_4981836 : CollatzResearch.WordTrace tailWord_4981836 prefixEnd_4981836 2558076409872275777438959 := by
  unfold tailWord_4981836
  simp only [CollatzResearch.WordTrace]
  refine ⟨90851243189833238347942681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121134990919777651130590241 90851243189833238347942681)
  ·
    refine ⟨68138432392374928760957011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90851243189833238347942681 68138432392374928760957011)
    ·
      refine ⟨102207648588562393141435517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68138432392374928760957011 102207648588562393141435517)
      ·
        refine ⟨38327868220710897428038319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102207648588562393141435517 38327868220710897428038319)
        ·
          refine ⟨57491802331066346142057479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38327868220710897428038319 57491802331066346142057479)
          ·
            refine ⟨86237703496599519213086219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57491802331066346142057479 86237703496599519213086219)
            ·
              refine ⟨129356555244899278819629329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86237703496599519213086219 129356555244899278819629329)
              ·
                refine ⟨97017416433674459114721997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129356555244899278819629329 97017416433674459114721997)
                ·
                  refine ⟨36381531162627922168020749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97017416433674459114721997 36381531162627922168020749)
                  ·
                    refine ⟨13643074185985470813007781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36381531162627922168020749 13643074185985470813007781)
                    ·
                      refine ⟨2558076409872275777438959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13643074185985470813007781 2558076409872275777438959)
                      ·
                        rfl

theorem cell23_4981836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_4981836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4981836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4981836 prefixEnd_4981836 := by exact prefixLift 4981836
  have htrace : WordTrace (prefixWord ++ tailWord_4981836) baseStart_4981836 baseEnd_4981836 := by
    simpa [prefixWord, tailWord_4981836, baseEnd_4981836] using wordTrace_append hprefix tailTrace_4981836
  have hstable : (prefixWord ++ tailWord_4981836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4981836).length < 2 ^ (prefixWord ++ tailWord_4981836).sum := by decide
  have hdescent : baseEnd_4981836 < baseStart_4981836 := by decide
  rcases family_descends (prefixWord ++ tailWord_4981836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4981837 : List Nat := [1, 6, 1, 1, 1, 2, 4, 2, 5]
def baseStart_4981837 : Nat := 118140960795 + 4981837 * 2 ^ 59
def prefixEnd_4981837 : Nat := 4983230072969 + 3 ^ 40 * 4981837 * 2
def baseEnd_4981837 : Nat := 284230769261436697058495

theorem tailTrace_4981837 : CollatzResearch.WordTrace tailWord_4981837 prefixEnd_4981837 284230769261436697058495 := by
  unfold tailWord_4981837
  simp only [CollatzResearch.WordTrace]
  refine ⟨181702522852662853866671765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121135015235108569244447843 181702522852662853866671765)
  ·
    refine ⟨8517305758718571275000239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 181702522852662853866671765 8517305758718571275000239)
    ·
      refine ⟨12775958638077856912500359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8517305758718571275000239 12775958638077856912500359)
      ·
        refine ⟨19163937957116785368750539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12775958638077856912500359 19163937957116785368750539)
        ·
          refine ⟨28745906935675178053125809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19163937957116785368750539 28745906935675178053125809)
          ·
            refine ⟨21559430201756383539844357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28745906935675178053125809 21559430201756383539844357)
            ·
              refine ⟨4042393162829321913720817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21559430201756383539844357 4042393162829321913720817)
              ·
                refine ⟨3031794872121991435290613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4042393162829321913720817 3031794872121991435290613)
                ·
                  refine ⟨284230769261436697058495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3031794872121991435290613 284230769261436697058495)
                  ·
                    rfl

theorem cell23_4981837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_4981837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4981837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4981837 prefixEnd_4981837 := by exact prefixLift 4981837
  have htrace : WordTrace (prefixWord ++ tailWord_4981837) baseStart_4981837 baseEnd_4981837 := by
    simpa [prefixWord, tailWord_4981837, baseEnd_4981837] using wordTrace_append hprefix tailTrace_4981837
  have hstable : (prefixWord ++ tailWord_4981837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4981837).length < 2 ^ (prefixWord ++ tailWord_4981837).sum := by decide
  have hdescent : baseEnd_4981837 < baseStart_4981837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4981837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4981863 : List Nat := [1, 1, 5, 1, 1, 3, 1, 1, 5, 4]
def baseStart_4981863 : Nat := 118140960795 + 4981863 * 2 ^ 59
def prefixEnd_4981863 : Nat := 4983230072969 + 3 ^ 40 * 4981863 * 2
def baseEnd_4981863 : Nat := 852696757949982390600445

theorem tailTrace_4981863 : CollatzResearch.WordTrace tailWord_4981863 prefixEnd_4981863 852696757949982390600445 := by
  unfold tailWord_4981863
  simp only [CollatzResearch.WordTrace]
  refine ⟨181703471150568660307118243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121135647433712440204745495 181703471150568660307118243)
  ·
    refine ⟨272555206725852990460677365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181703471150568660307118243 272555206725852990460677365)
    ·
      refine ⟨25552050630548717855688503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 272555206725852990460677365 25552050630548717855688503)
      ·
        refine ⟨38328075945823076783532755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25552050630548717855688503 38328075945823076783532755)
        ·
          refine ⟨57492113918734615175299133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38328075945823076783532755 57492113918734615175299133)
          ·
            refine ⟨21559542719525480690737175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57492113918734615175299133 21559542719525480690737175)
            ·
              refine ⟨32339314079288221036105763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21559542719525480690737175 32339314079288221036105763)
              ·
                refine ⟨48508971118932331554158645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32339314079288221036105763 48508971118932331554158645)
                ·
                  refine ⟨4547716042399906083202373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48508971118932331554158645 4547716042399906083202373)
                  ·
                    refine ⟨852696757949982390600445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4547716042399906083202373 852696757949982390600445)
                    ·
                      rfl

theorem cell23_4981863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_4981863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4981863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4981863 prefixEnd_4981863 := by exact prefixLift 4981863
  have htrace : WordTrace (prefixWord ++ tailWord_4981863) baseStart_4981863 baseEnd_4981863 := by
    simpa [prefixWord, tailWord_4981863, baseEnd_4981863] using wordTrace_append hprefix tailTrace_4981863
  have hstable : (prefixWord ++ tailWord_4981863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4981863).length < 2 ^ (prefixWord ++ tailWord_4981863).sum := by decide
  have hdescent : baseEnd_4981863 < baseStart_4981863 := by decide
  rcases family_descends (prefixWord ++ tailWord_4981863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4981870 : List Nat := [4, 1, 2, 2, 1, 2, 3, 1, 2, 1, 4]
def baseStart_4981870 : Nat := 118140960795 + 4981870 * 2 ^ 59
def prefixEnd_4981870 : Nat := 4983230072969 + 3 ^ 40 * 4981870 * 2
def baseEnd_4981870 : Nat := 2558093868214528644413803

theorem tailTrace_4981870 : CollatzResearch.WordTrace tailWord_4981870 prefixEnd_4981870 2558093868214528644413803 := by
  unfold tailWord_4981870
  simp only [CollatzResearch.WordTrace]
  refine ⟨22712965807692912562827883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121135817641028867001748709 22712965807692912562827883)
  ·
    refine ⟨34069448711539368844241825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22712965807692912562827883 34069448711539368844241825)
    ·
      refine ⟨25552086533654526633181369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34069448711539368844241825 25552086533654526633181369)
      ·
        refine ⟨19164064900240894974886027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25552086533654526633181369 19164064900240894974886027)
        ·
          refine ⟨28746097350361342462329041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19164064900240894974886027 28746097350361342462329041)
          ·
            refine ⟨21559573012771006846746781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28746097350361342462329041 21559573012771006846746781)
            ·
              refine ⟨8084839879789127567530043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21559573012771006846746781 8084839879789127567530043)
              ·
                refine ⟨12127259819683691351295065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8084839879789127567530043 12127259819683691351295065)
                ·
                  refine ⟨9095444864762768513471299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12127259819683691351295065 9095444864762768513471299)
                  ·
                    refine ⟨13643167297144152770206949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9095444864762768513471299 13643167297144152770206949)
                    ·
                      refine ⟨2558093868214528644413803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13643167297144152770206949 2558093868214528644413803)
                      ·
                        rfl

theorem cell23_4981870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_4981870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4981870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4981870 prefixEnd_4981870 := by exact prefixLift 4981870
  have htrace : WordTrace (prefixWord ++ tailWord_4981870) baseStart_4981870 baseEnd_4981870 := by
    simpa [prefixWord, tailWord_4981870, baseEnd_4981870] using wordTrace_append hprefix tailTrace_4981870
  have hstable : (prefixWord ++ tailWord_4981870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4981870).length < 2 ^ (prefixWord ++ tailWord_4981870).sum := by decide
  have hdescent : baseEnd_4981870 < baseStart_4981870 := by decide
  rcases family_descends (prefixWord ++ tailWord_4981870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4981873 : List Nat := [1, 2, 2, 2, 1, 1, 2, 5, 2, 2, 3]
def baseStart_4981873 : Nat := 118140960795 + 4981873 * 2 ^ 59
def prefixEnd_4981873 : Nat := 4983230072969 + 3 ^ 40 * 4981873 * 2
def baseEnd_4981873 : Nat := 2558095408656492132676289

theorem tailTrace_4981873 : CollatzResearch.WordTrace tailWord_4981873 prefixEnd_4981873 2558095408656492132676289 := by
  unfold tailWord_4981873
  simp only [CollatzResearch.WordTrace]
  refine ⟨181703835880532432014982273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121135890587021621343321515 181703835880532432014982273)
  ·
    refine ⟨136277876910399324011236705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181703835880532432014982273 136277876910399324011236705)
    ·
      refine ⟨102208407682799493008427529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136277876910399324011236705 102208407682799493008427529)
      ·
        refine ⟨76656305762099619756320647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102208407682799493008427529 76656305762099619756320647)
        ·
          refine ⟨114984458643149429634480971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76656305762099619756320647 114984458643149429634480971)
          ·
            refine ⟨172476687964724144451721457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114984458643149429634480971 172476687964724144451721457)
            ·
              refine ⟨129357515973543108338791093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 172476687964724144451721457 129357515973543108338791093)
              ·
                refine ⟨12127267122519666406761665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 129357515973543108338791093 12127267122519666406761665)
                ·
                  refine ⟨9095450341889749805071249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12127267122519666406761665 9095450341889749805071249)
                  ·
                    refine ⟨6821587756417312353803437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9095450341889749805071249 6821587756417312353803437)
                    ·
                      refine ⟨2558095408656492132676289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6821587756417312353803437 2558095408656492132676289)
                      ·
                        rfl

theorem cell23_4981873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5, 2, 2, 3].length) (baseStart_4981873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4981873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4981873 prefixEnd_4981873 := by exact prefixLift 4981873
  have htrace : WordTrace (prefixWord ++ tailWord_4981873) baseStart_4981873 baseEnd_4981873 := by
    simpa [prefixWord, tailWord_4981873, baseEnd_4981873] using wordTrace_append hprefix tailTrace_4981873
  have hstable : (prefixWord ++ tailWord_4981873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4981873).length < 2 ^ (prefixWord ++ tailWord_4981873).sum := by decide
  have hdescent : baseEnd_4981873 < baseStart_4981873 := by decide
  rcases family_descends (prefixWord ++ tailWord_4981873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4981880 : List Nat := [2, 1, 2, 1, 1, 1, 5, 5, 1, 4]
def baseStart_4981880 : Nat := 118140960795 + 4981880 * 2 ^ 59
def prefixEnd_4981880 : Nat := 4983230072969 + 3 ^ 40 * 4981880 * 2
def baseEnd_4981880 : Nat := 852699667673691201762919

theorem tailTrace_4981880 : CollatzResearch.WordTrace tailWord_4981880 prefixEnd_4981880 852699667673691201762919 := by
  unfold tailWord_4981880
  simp only [CollatzResearch.WordTrace]
  refine ⟨90852045595753536105243547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121136060794338048140324729 90852045595753536105243547)
  ·
    refine ⟨136278068393630304157865321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90852045595753536105243547 136278068393630304157865321)
    ·
      refine ⟨102208551295222728118398991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136278068393630304157865321 102208551295222728118398991)
      ·
        refine ⟨153312826942834092177598487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102208551295222728118398991 153312826942834092177598487)
        ·
          refine ⟨229969240414251138266397731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153312826942834092177598487 229969240414251138266397731)
          ·
            refine ⟨344953860621376707399596597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229969240414251138266397731 344953860621376707399596597)
            ·
              refine ⟨32339424433254066318712181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 344953860621376707399596597 32339424433254066318712181)
              ·
                refine ⟨3031821040617568717379267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32339424433254066318712181 3031821040617568717379267)
                ·
                  refine ⟨4547731560926353076068901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3031821040617568717379267 4547731560926353076068901)
                  ·
                    refine ⟨852699667673691201762919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4547731560926353076068901 852699667673691201762919)
                    ·
                      rfl

theorem cell23_4981880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 5, 1, 4].length) (baseStart_4981880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4981880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4981880 prefixEnd_4981880 := by exact prefixLift 4981880
  have htrace : WordTrace (prefixWord ++ tailWord_4981880) baseStart_4981880 baseEnd_4981880 := by
    simpa [prefixWord, tailWord_4981880, baseEnd_4981880] using wordTrace_append hprefix tailTrace_4981880
  have hstable : (prefixWord ++ tailWord_4981880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4981880).length < 2 ^ (prefixWord ++ tailWord_4981880).sum := by decide
  have hdescent : baseEnd_4981880 < baseStart_4981880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4981880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4981893 : List Nat := [1, 3, 1, 1, 6, 1, 1, 1, 8]
def baseStart_4981893 : Nat := 118140960795 + 4981893 * 2 ^ 59
def prefixEnd_4981893 : Nat := 4983230072969 + 3 ^ 40 * 4981893 * 2
def baseEnd_4981893 : Nat := 284233964252175783825133

theorem tailTrace_4981893 : CollatzResearch.WordTrace tailWord_4981893 prefixEnd_4981893 284233964252175783825133 := by
  unfold tailWord_4981893
  simp only [CollatzResearch.WordTrace]
  refine ⟨181704565340459975430710333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121136376893639983620473555 181704565340459975430710333)
  ·
    refine ⟨68139212002672490786516375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181704565340459975430710333 68139212002672490786516375)
    ·
      refine ⟨102208818004008736179774563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68139212002672490786516375 102208818004008736179774563)
      ·
        refine ⟨153313227006013104269661845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102208818004008736179774563 153313227006013104269661845)
        ·
          refine ⟨7186557515906864262640399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 153313227006013104269661845 7186557515906864262640399)
          ·
            refine ⟨10779836273860296393960599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7186557515906864262640399 10779836273860296393960599)
            ·
              refine ⟨16169754410790444590940899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10779836273860296393960599 16169754410790444590940899)
              ·
                refine ⟨24254631616185666886411349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16169754410790444590940899 24254631616185666886411349)
                ·
                  refine ⟨284233964252175783825133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24254631616185666886411349 284233964252175783825133)
                  ·
                    rfl

theorem cell23_4981893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 8].length) (baseStart_4981893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4981893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4981893 prefixEnd_4981893 := by exact prefixLift 4981893
  have htrace : WordTrace (prefixWord ++ tailWord_4981893) baseStart_4981893 baseEnd_4981893 := by
    simpa [prefixWord, tailWord_4981893, baseEnd_4981893] using wordTrace_append hprefix tailTrace_4981893
  have hstable : (prefixWord ++ tailWord_4981893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4981893).length < 2 ^ (prefixWord ++ tailWord_4981893).sum := by decide
  have hdescent : baseEnd_4981893 < baseStart_4981893 := by decide
  rcases family_descends (prefixWord ++ tailWord_4981893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4981920 : List Nat := [2, 1, 1, 4, 2, 1, 1, 4, 3, 1, 3]
def baseStart_4981920 : Nat := 118140960795 + 4981920 * 2 ^ 59
def prefixEnd_4981920 : Nat := 4983230072969 + 3 ^ 40 * 4981920 * 2
def baseEnd_4981920 : Nat := 2558119542247253448788573

theorem tailTrace_4981920 : CollatzResearch.WordTrace tailWord_4981920 prefixEnd_4981920 2558119542247253448788573 := by
  unfold tailWord_4981920
  simp only [CollatzResearch.WordTrace]
  refine ⟨90852775055681079520971607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121137033407574772694628809 90852775055681079520971607)
  ·
    refine ⟨136279162583521619281457411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90852775055681079520971607 136279162583521619281457411)
    ·
      refine ⟨204418743875282428922186117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136279162583521619281457411 204418743875282428922186117)
      ·
        refine ⟨38328514476615455422909897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 204418743875282428922186117 38328514476615455422909897)
        ·
          refine ⟨28746385857461591567182423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38328514476615455422909897 28746385857461591567182423)
          ·
            refine ⟨43119578786192387350773635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28746385857461591567182423 43119578786192387350773635)
            ·
              refine ⟨64679368179288581026160453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43119578786192387350773635 64679368179288581026160453)
              ·
                refine ⟨12127381533616608942405085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64679368179288581026160453 12127381533616608942405085)
                ·
                  refine ⟨4547768075106228353401907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12127381533616608942405085 4547768075106228353401907)
                  ·
                    refine ⟨6821652112659342530102861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4547768075106228353401907 6821652112659342530102861)
                    ·
                      refine ⟨2558119542247253448788573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6821652112659342530102861 2558119542247253448788573)
                      ·
                        rfl

theorem cell23_4981920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4, 3, 1, 3].length) (baseStart_4981920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4981920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4981920 prefixEnd_4981920 := by exact prefixLift 4981920
  have htrace : WordTrace (prefixWord ++ tailWord_4981920) baseStart_4981920 baseEnd_4981920 := by
    simpa [prefixWord, tailWord_4981920, baseEnd_4981920] using wordTrace_append hprefix tailTrace_4981920
  have hstable : (prefixWord ++ tailWord_4981920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4981920).length < 2 ^ (prefixWord ++ tailWord_4981920).sum := by decide
  have hdescent : baseEnd_4981920 < baseStart_4981920 := by decide
  rcases family_descends (prefixWord ++ tailWord_4981920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4981997 : List Nat := [1, 5, 1, 2, 2, 3, 1, 1, 1, 1, 5]
def baseStart_4981997 : Nat := 118140960795 + 4981997 * 2 ^ 59
def prefixEnd_4981997 : Nat := 4983230072969 + 3 ^ 40 * 4981997 * 2
def baseEnd_4981997 : Nat := 2558159080257649647525719

theorem tailTrace_4981997 : CollatzResearch.WordTrace tailWord_4981997 prefixEnd_4981997 2558159080257649647525719 := by
  unfold tailWord_4981997
  simp only [CollatzResearch.WordTrace]
  refine ⟨181708358532083201192496245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121138905688055467461664163 181708358532083201192496245)
  ·
    refine ⟨17035158612382800111796523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 181708358532083201192496245 17035158612382800111796523)
    ·
      refine ⟨25552737918574200167694785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17035158612382800111796523 25552737918574200167694785)
      ·
        refine ⟨19164553438930650125771089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25552737918574200167694785 19164553438930650125771089)
        ·
          refine ⟨14373415079197987594328317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19164553438930650125771089 14373415079197987594328317)
          ·
            refine ⟨5390030654699245347873119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14373415079197987594328317 5390030654699245347873119)
            ·
              refine ⟨8085045982048868021809679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5390030654699245347873119 8085045982048868021809679)
              ·
                refine ⟨12127568973073302032714519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8085045982048868021809679 12127568973073302032714519)
                ·
                  refine ⟨18191353459609953049071779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12127568973073302032714519 18191353459609953049071779)
                  ·
                    refine ⟨27287030189414929573607669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18191353459609953049071779 27287030189414929573607669)
                    ·
                      refine ⟨2558159080257649647525719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27287030189414929573607669 2558159080257649647525719)
                      ·
                        rfl

theorem cell23_4981997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_4981997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4981997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4981997 prefixEnd_4981997 := by exact prefixLift 4981997
  have htrace : WordTrace (prefixWord ++ tailWord_4981997) baseStart_4981997 baseEnd_4981997 := by
    simpa [prefixWord, tailWord_4981997, baseEnd_4981997] using wordTrace_append hprefix tailTrace_4981997
  have hstable : (prefixWord ++ tailWord_4981997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4981997).length < 2 ^ (prefixWord ++ tailWord_4981997).sum := by decide
  have hdescent : baseEnd_4981997 < baseStart_4981997 := by decide
  rcases family_descends (prefixWord ++ tailWord_4981997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4982027 : List Nat := [1, 1, 1, 1, 5, 3, 2, 3, 2, 1, 3]
def baseStart_4982027 : Nat := 118140960795 + 4982027 * 2 ^ 59
def prefixEnd_4982027 : Nat := 4983230072969 + 3 ^ 40 * 4982027 * 2
def baseEnd_4982027 : Nat := 2558174484677284530150581

theorem tailTrace_4982027 : CollatzResearch.WordTrace tailWord_4982027 prefixEnd_4982027 2558174484677284530150581 := by
  unfold tailWord_4982027
  simp only [CollatzResearch.WordTrace]
  refine ⟨181709452721974516316088335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121139635147983010877392223 181709452721974516316088335)
  ·
    refine ⟨272564179082961774474132503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181709452721974516316088335 272564179082961774474132503)
    ·
      refine ⟨408846268624442661711198755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272564179082961774474132503 408846268624442661711198755)
      ·
        refine ⟨613269402936663992566798133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 408846268624442661711198755 613269402936663992566798133)
        ·
          refine ⟨57494006525312249303137325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 613269402936663992566798133 57494006525312249303137325)
          ·
            refine ⟨21560252446992093488676497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57494006525312249303137325 21560252446992093488676497)
            ·
              refine ⟨16170189335244070116507373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21560252446992093488676497 16170189335244070116507373)
              ·
                refine ⟨6063821000716526293690265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16170189335244070116507373 6063821000716526293690265)
                ·
                  refine ⟨4547865750537394720267699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6063821000716526293690265 4547865750537394720267699)
                  ·
                    refine ⟨6821798625806092080401549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4547865750537394720267699 6821798625806092080401549)
                    ·
                      refine ⟨2558174484677284530150581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6821798625806092080401549 2558174484677284530150581)
                      ·
                        rfl

theorem cell23_4982027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 3, 2, 1, 3].length) (baseStart_4982027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4982027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4982027 prefixEnd_4982027 := by exact prefixLift 4982027
  have htrace : WordTrace (prefixWord ++ tailWord_4982027) baseStart_4982027 baseEnd_4982027 := by
    simpa [prefixWord, tailWord_4982027, baseEnd_4982027] using wordTrace_append hprefix tailTrace_4982027
  have hstable : (prefixWord ++ tailWord_4982027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4982027).length < 2 ^ (prefixWord ++ tailWord_4982027).sum := by decide
  have hdescent : baseEnd_4982027 < baseStart_4982027 := by decide
  rcases family_descends (prefixWord ++ tailWord_4982027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4982033 : List Nat := [1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 4]
def baseStart_4982033 : Nat := 118140960795 + 4982033 * 2 ^ 59
def prefixEnd_4982033 : Nat := 4983230072969 + 3 ^ 40 * 4982033 * 2
def baseEnd_4982033 : Nat := 2558177565561211506675553

theorem tailTrace_4982033 : CollatzResearch.WordTrace tailWord_4982033 prefixEnd_4982033 2558177565561211506675553 := by
  unfold tailWord_4982033
  simp only [CollatzResearch.WordTrace]
  refine ⟨181709671559952779340806753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121139781039968519560537835 181709671559952779340806753)
  ·
    refine ⟨136282253669964584505605065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181709671559952779340806753 136282253669964584505605065)
    ·
      refine ⟨102211690252473438379203799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136282253669964584505605065 102211690252473438379203799)
      ·
        refine ⟨153317535378710157568805699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102211690252473438379203799 153317535378710157568805699)
        ·
          refine ⟨229976303068065236353208549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153317535378710157568805699 229976303068065236353208549)
          ·
            refine ⟨43120556825262231816226603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 229976303068065236353208549 43120556825262231816226603)
            ·
              refine ⟨64680835237893347724339905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43120556825262231816226603 64680835237893347724339905)
              ·
                refine ⟨48510626428420010793254929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64680835237893347724339905 48510626428420010793254929)
                ·
                  refine ⟨36382969821315008094941197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48510626428420010793254929 36382969821315008094941197)
                  ·
                    refine ⟨13643613682993128035602949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36382969821315008094941197 13643613682993128035602949)
                    ·
                      refine ⟨2558177565561211506675553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13643613682993128035602949 2558177565561211506675553)
                      ·
                        rfl

theorem cell23_4982033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 4].length) (baseStart_4982033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4982033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4982033 prefixEnd_4982033 := by exact prefixLift 4982033
  have htrace : WordTrace (prefixWord ++ tailWord_4982033) baseStart_4982033 baseEnd_4982033 := by
    simpa [prefixWord, tailWord_4982033, baseEnd_4982033] using wordTrace_append hprefix tailTrace_4982033
  have hstable : (prefixWord ++ tailWord_4982033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4982033).length < 2 ^ (prefixWord ++ tailWord_4982033).sum := by decide
  have hdescent : baseEnd_4982033 < baseStart_4982033 := by decide
  rcases family_descends (prefixWord ++ tailWord_4982033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4982034 : List Nat := [3, 2, 4, 2, 1, 1, 3, 7]
def baseStart_4982034 : Nat := 118140960795 + 4982034 * 2 ^ 59
def prefixEnd_4982034 : Nat := 4983230072969 + 3 ^ 40 * 4982034 * 2
def baseEnd_4982034 : Nat := 94747336260809851954187

theorem tailTrace_4982034 : CollatzResearch.WordTrace tailWord_4982034 prefixEnd_4982034 94747336260809851954187 := by
  unfold tailWord_4982034
  simp only [CollatzResearch.WordTrace]
  refine ⟨45427427008237289127898289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121139805355299437674395437 45427427008237289127898289)
  ·
    refine ⟨34070570256177966845923717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45427427008237289127898289 34070570256177966845923717)
    ·
      refine ⟨6388231923033368783610697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34070570256177966845923717 6388231923033368783610697)
      ·
        refine ⟨4791173942275026587708023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6388231923033368783610697 4791173942275026587708023)
        ·
          refine ⟨7186760913412539881562035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4791173942275026587708023 7186760913412539881562035)
          ·
            refine ⟨10780141370118809822343053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7186760913412539881562035 10780141370118809822343053)
            ·
              refine ⟨4042553013794553683378645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10780141370118809822343053 4042553013794553683378645)
              ·
                refine ⟨94747336260809851954187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4042553013794553683378645 94747336260809851954187)
                ·
                  rfl

theorem cell23_4982034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 7].length) (baseStart_4982034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4982034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4982034 prefixEnd_4982034 := by exact prefixLift 4982034
  have htrace : WordTrace (prefixWord ++ tailWord_4982034) baseStart_4982034 baseEnd_4982034 := by
    simpa [prefixWord, tailWord_4982034, baseEnd_4982034] using wordTrace_append hprefix tailTrace_4982034
  have hstable : (prefixWord ++ tailWord_4982034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4982034).length < 2 ^ (prefixWord ++ tailWord_4982034).sum := by decide
  have hdescent : baseEnd_4982034 < baseStart_4982034 := by decide
  rcases family_descends (prefixWord ++ tailWord_4982034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4982037 : List Nat := [1, 3, 2, 1, 2, 1, 1, 6, 1, 3, 2]
def baseStart_4982037 : Nat := 118140960795 + 4982037 * 2 ^ 59
def prefixEnd_4982037 : Nat := 4983230072969 + 3 ^ 40 * 4982037 * 2
def baseEnd_4982037 : Nat := 2558179619483829491025535

theorem tailTrace_4982037 : CollatzResearch.WordTrace tailWord_4982037 prefixEnd_4982037 2558179619483829491025535 := by
  unfold tailWord_4982037
  simp only [CollatzResearch.WordTrace]
  refine ⟨181709817451938288023952365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121139878301292192015968243 181709817451938288023952365)
  ·
    refine ⟨68141181544476858008982137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181709817451938288023952365 68141181544476858008982137)
    ·
      refine ⟨51105886158357643506736603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68141181544476858008982137 51105886158357643506736603)
      ·
        refine ⟨76658829237536465260104905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51105886158357643506736603 76658829237536465260104905)
        ·
          refine ⟨57494121928152348945078679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76658829237536465260104905 57494121928152348945078679)
          ·
            refine ⟨86241182892228523417618019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57494121928152348945078679 86241182892228523417618019)
            ·
              refine ⟨129361774338342785126427029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86241182892228523417618019 129361774338342785126427029)
              ·
                refine ⟨6063833172109818052801267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 129361774338342785126427029 6063833172109818052801267)
                ·
                  refine ⟨9095749758164727079201901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6063833172109818052801267 9095749758164727079201901)
                  ·
                    refine ⟨3410906159311772654700713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9095749758164727079201901 3410906159311772654700713)
                    ·
                      refine ⟨2558179619483829491025535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3410906159311772654700713 2558179619483829491025535)
                      ·
                        rfl

theorem cell23_4982037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 6, 1, 3, 2].length) (baseStart_4982037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4982037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4982037 prefixEnd_4982037 := by exact prefixLift 4982037
  have htrace : WordTrace (prefixWord ++ tailWord_4982037) baseStart_4982037 baseEnd_4982037 := by
    simpa [prefixWord, tailWord_4982037, baseEnd_4982037] using wordTrace_append hprefix tailTrace_4982037
  have hstable : (prefixWord ++ tailWord_4982037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4982037).length < 2 ^ (prefixWord ++ tailWord_4982037).sum := by decide
  have hdescent : baseEnd_4982037 < baseStart_4982037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4982037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4982061 : List Nat := [1, 5, 3, 1, 1, 1, 3, 2, 2, 1, 3]
def baseStart_4982061 : Nat := 118140960795 + 4982061 * 2 ^ 59
def prefixEnd_4982061 : Nat := 4983230072969 + 3 ^ 40 * 4982061 * 2
def baseEnd_4982061 : Nat := 2558191943019537397125425

theorem tailTrace_4982061 : CollatzResearch.WordTrace tailWord_4982061 prefixEnd_4982061 2558191943019537397125425 := by
  unfold tailWord_4982061
  simp only [CollatzResearch.WordTrace]
  refine ⟨181710692803851340122826037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121140461869234226748550691 181710692803851340122826037)
  ·
    refine ⟨17035377450361063136514941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 181710692803851340122826037 17035377450361063136514941)
    ·
      refine ⟨6388266543885398676193103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17035377450361063136514941 6388266543885398676193103)
      ·
        refine ⟨9582399815828098014289655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6388266543885398676193103 9582399815828098014289655)
        ·
          refine ⟨14373599723742147021434483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9582399815828098014289655 14373599723742147021434483)
          ·
            refine ⟨21560399585613220532151725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14373599723742147021434483 21560399585613220532151725)
            ·
              refine ⟨8085149844604957699556897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21560399585613220532151725 8085149844604957699556897)
              ·
                refine ⟨6063862383453718274667673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8085149844604957699556897 6063862383453718274667673)
                ·
                  refine ⟨4547896787590288706000755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6063862383453718274667673 4547896787590288706000755)
                  ·
                    refine ⟨6821845181385433059001133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4547896787590288706000755 6821845181385433059001133)
                    ·
                      refine ⟨2558191943019537397125425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6821845181385433059001133 2558191943019537397125425)
                      ·
                        rfl

theorem cell23_4982061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_4982061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4982061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4982061 prefixEnd_4982061 := by exact prefixLift 4982061
  have htrace : WordTrace (prefixWord ++ tailWord_4982061) baseStart_4982061 baseEnd_4982061 := by
    simpa [prefixWord, tailWord_4982061, baseEnd_4982061] using wordTrace_append hprefix tailTrace_4982061
  have hstable : (prefixWord ++ tailWord_4982061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4982061).length < 2 ^ (prefixWord ++ tailWord_4982061).sum := by decide
  have hdescent : baseEnd_4982061 < baseStart_4982061 := by decide
  rcases family_descends (prefixWord ++ tailWord_4982061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4982113 : List Nat := [1, 2, 3, 1, 1, 1, 1, 2, 3, 1, 7]
def baseStart_4982113 : Nat := 118140960795 + 4982113 * 2 ^ 59
def prefixEnd_4982113 : Nat := 4983230072969 + 3 ^ 40 * 4982113 * 2
def baseEnd_4982113 : Nat := 2558218644013571193675185

theorem tailTrace_4982113 : CollatzResearch.WordTrace tailWord_4982113 prefixEnd_4982113 2558218644013571193675185 := by
  unfold tailWord_4982113
  simp only [CollatzResearch.WordTrace]
  refine ⟨181712589399662953003718993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121141726266441968669145995 181712589399662953003718993)
  ·
    refine ⟨136284442049747214752789245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181712589399662953003718993 136284442049747214752789245)
    ·
      refine ⟨51106665768655205532295967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136284442049747214752789245 51106665768655205532295967)
      ·
        refine ⟨76659998652982808298443951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51106665768655205532295967 76659998652982808298443951)
        ·
          refine ⟨114989997979474212447665927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76659998652982808298443951 114989997979474212447665927)
          ·
            refine ⟨172484996969211318671498891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114989997979474212447665927 172484996969211318671498891)
            ·
              refine ⟨258727495453816978007248337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172484996969211318671498891 258727495453816978007248337)
              ·
                refine ⟨194045621590362733505436253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 258727495453816978007248337 194045621590362733505436253)
                ·
                  refine ⟨72767108096386025064538595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 194045621590362733505436253 72767108096386025064538595)
                  ·
                    refine ⟨109150662144579037596807893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 72767108096386025064538595 109150662144579037596807893)
                    ·
                      refine ⟨2558218644013571193675185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 109150662144579037596807893 2558218644013571193675185)
                      ·
                        rfl

theorem cell23_4982113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_4982113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4982113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4982113 prefixEnd_4982113 := by exact prefixLift 4982113
  have htrace : WordTrace (prefixWord ++ tailWord_4982113) baseStart_4982113 baseEnd_4982113 := by
    simpa [prefixWord, tailWord_4982113, baseEnd_4982113] using wordTrace_append hprefix tailTrace_4982113
  have hstable : (prefixWord ++ tailWord_4982113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4982113).length < 2 ^ (prefixWord ++ tailWord_4982113).sum := by decide
  have hdescent : baseEnd_4982113 < baseStart_4982113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4982113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4982124 : List Nat := [2, 2, 1, 1, 5, 2, 3, 2, 5]
def baseStart_4982124 : Nat := 118140960795 + 4982124 * 2 ^ 59
def prefixEnd_4982124 : Nat := 4983230072969 + 3 ^ 40 * 4982124 * 2
def baseEnd_4982124 : Nat := 284247143588974516737515

theorem tailTrace_4982124 : CollatzResearch.WordTrace tailWord_4982124 prefixEnd_4982124 284247143588974516737515 := by
  unfold tailWord_4982124
  simp only [CollatzResearch.WordTrace]
  refine ⟨90856495301311550941184713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121141993735082067921579617 90856495301311550941184713)
  ·
    refine ⟨68142371475983663205888535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90856495301311550941184713 68142371475983663205888535)
    ·
      refine ⟨102213557213975494808832803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68142371475983663205888535 102213557213975494808832803)
      ·
        refine ⟨153320335820963242213249205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102213557213975494808832803 153320335820963242213249205)
        ·
          refine ⟨14373781483215303957492113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 153320335820963242213249205 14373781483215303957492113)
          ·
            refine ⟨10780336112411477968119085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14373781483215303957492113 10780336112411477968119085)
            ·
              refine ⟨4042626042154304238044657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10780336112411477968119085 4042626042154304238044657)
              ·
                refine ⟨3031969531615728178533493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4042626042154304238044657 3031969531615728178533493)
                ·
                  refine ⟨284247143588974516737515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3031969531615728178533493 284247143588974516737515)
                  ·
                    rfl

theorem cell23_4982124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 2, 5].length) (baseStart_4982124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4982124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4982124 prefixEnd_4982124 := by exact prefixLift 4982124
  have htrace : WordTrace (prefixWord ++ tailWord_4982124) baseStart_4982124 baseEnd_4982124 := by
    simpa [prefixWord, tailWord_4982124, baseEnd_4982124] using wordTrace_append hprefix tailTrace_4982124
  have hstable : (prefixWord ++ tailWord_4982124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4982124).length < 2 ^ (prefixWord ++ tailWord_4982124).sum := by decide
  have hdescent : baseEnd_4982124 < baseStart_4982124 := by decide
  rcases family_descends (prefixWord ++ tailWord_4982124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4982130 : List Nat := [3, 2, 1, 2, 1, 2, 3, 1, 1, 2, 5]
def baseStart_4982130 : Nat := 118140960795 + 4982130 * 2 ^ 59
def prefixEnd_4982130 : Nat := 4983230072969 + 3 ^ 40 * 4982130 * 2
def baseEnd_4982130 : Nat := 2558227373184697627162607

theorem tailTrace_4982130 : CollatzResearch.WordTrace tailWord_4982130 prefixEnd_4982130 2558227373184697627162607 := by
  unfold tailWord_4982130
  simp only [CollatzResearch.WordTrace]
  refine ⟨45428302360150341226771961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121142139627067576604725229 45428302360150341226771961)
  ·
    refine ⟨34071226770112755920078971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45428302360150341226771961 34071226770112755920078971)
    ·
      refine ⟨51106840155169133880118457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34071226770112755920078971 51106840155169133880118457)
      ·
        refine ⟨38330130116376850410088843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51106840155169133880118457 38330130116376850410088843)
        ·
          refine ⟨57495195174565275615133265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38330130116376850410088843 57495195174565275615133265)
          ·
            refine ⟨43121396380923956711349949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57495195174565275615133265 43121396380923956711349949)
            ·
              refine ⟨16170523642846483766756231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43121396380923956711349949 16170523642846483766756231)
              ·
                refine ⟨24255785464269725650134347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16170523642846483766756231 24255785464269725650134347)
                ·
                  refine ⟨36383678196404588475201521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24255785464269725650134347 36383678196404588475201521)
                  ·
                    refine ⟨27287758647303441356401141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36383678196404588475201521 27287758647303441356401141)
                    ·
                      refine ⟨2558227373184697627162607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27287758647303441356401141 2558227373184697627162607)
                      ·
                        rfl

theorem cell23_4982130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_4982130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4982130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4982130 prefixEnd_4982130 := by exact prefixLift 4982130
  have htrace : WordTrace (prefixWord ++ tailWord_4982130) baseStart_4982130 baseEnd_4982130 := by
    simpa [prefixWord, tailWord_4982130, baseEnd_4982130] using wordTrace_append hprefix tailTrace_4982130
  have hstable : (prefixWord ++ tailWord_4982130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4982130).length < 2 ^ (prefixWord ++ tailWord_4982130).sum := by decide
  have hdescent : baseEnd_4982130 < baseStart_4982130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4982130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4982140 : List Nat := [2, 2, 2, 1, 1, 1, 3, 2, 4, 1, 4]
def baseStart_4982140 : Nat := 118140960795 + 4982140 * 2 ^ 59
def prefixEnd_4982140 : Nat := 4983230072969 + 3 ^ 40 * 4982140 * 2
def baseEnd_4982140 : Nat := 2558232507991242588037561

theorem tailTrace_4982140 : CollatzResearch.WordTrace tailWord_4982140 prefixEnd_4982140 2558232507991242588037561 := by
  unfold tailWord_4982140
  simp only [CollatzResearch.WordTrace]
  refine ⟨90856787085282568307475937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121142382780376757743301249 90856787085282568307475937)
  ·
    refine ⟨68142590313961926230606953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90856787085282568307475937 68142590313961926230606953)
    ·
      refine ⟨51106942735471444672955215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68142590313961926230606953 51106942735471444672955215)
      ·
        refine ⟨76660414103207167009432823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51106942735471444672955215 76660414103207167009432823)
        ·
          refine ⟨114990621154810750514149235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76660414103207167009432823 114990621154810750514149235)
          ·
            refine ⟨172485931732216125771223853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114990621154810750514149235 172485931732216125771223853)
            ·
              refine ⟨64682224399581047164208945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 172485931732216125771223853 64682224399581047164208945)
              ·
                refine ⟨48511668299685785373156709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64682224399581047164208945 48511668299685785373156709)
                ·
                  refine ⟨9095937806191084757466883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48511668299685785373156709 9095937806191084757466883)
                  ·
                    refine ⟨13643906709286627136200325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9095937806191084757466883 13643906709286627136200325)
                    ·
                      refine ⟨2558232507991242588037561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13643906709286627136200325 2558232507991242588037561)
                      ·
                        rfl

theorem cell23_4982140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 4, 1, 4].length) (baseStart_4982140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4982140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4982140 prefixEnd_4982140 := by exact prefixLift 4982140
  have htrace : WordTrace (prefixWord ++ tailWord_4982140) baseStart_4982140 baseEnd_4982140 := by
    simpa [prefixWord, tailWord_4982140, baseEnd_4982140] using wordTrace_append hprefix tailTrace_4982140
  have hstable : (prefixWord ++ tailWord_4982140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4982140).length < 2 ^ (prefixWord ++ tailWord_4982140).sum := by decide
  have hdescent : baseEnd_4982140 < baseStart_4982140 := by decide
  rcases family_descends (prefixWord ++ tailWord_4982140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4982170 : List Nat := [3, 1, 1, 4, 1, 1, 2, 1, 2, 1, 6]
def baseStart_4982170 : Nat := 118140960795 + 4982170 * 2 ^ 59
def prefixEnd_4982170 : Nat := 4983230072969 + 3 ^ 40 * 4982170 * 2
def baseEnd_4982170 : Nat := 2558247912410877470662423

theorem tailTrace_4982170 : CollatzResearch.WordTrace tailWord_4982170 prefixEnd_4982170 2558247912410877470662423 := by
  unfold tailWord_4982170
  simp only [CollatzResearch.WordTrace]
  refine ⟨45428667090114112934635991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121143112240304301159029309 45428667090114112934635991)
  ·
    refine ⟨68143000635171169401953987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45428667090114112934635991 68143000635171169401953987)
    ·
      refine ⟨102214500952756754102930981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68143000635171169401953987 102214500952756754102930981)
      ·
        refine ⟨19165218928641891394299559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102214500952756754102930981 19165218928641891394299559)
        ·
          refine ⟨28747828392962837091449339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19165218928641891394299559 28747828392962837091449339)
          ·
            refine ⟨43121742589444255637174009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28747828392962837091449339 43121742589444255637174009)
            ·
              refine ⟨32341306942083191727880507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43121742589444255637174009 32341306942083191727880507)
              ·
                refine ⟨48511960413124787591820761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32341306942083191727880507 48511960413124787591820761)
                ·
                  refine ⟨36383970309843590693865571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48511960413124787591820761 36383970309843590693865571)
                  ·
                    refine ⟨54575955464765386040798357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36383970309843590693865571 54575955464765386040798357)
                    ·
                      refine ⟨2558247912410877470662423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54575955464765386040798357 2558247912410877470662423)
                      ·
                        rfl

theorem cell23_4982170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_4982170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4982170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4982170 prefixEnd_4982170 := by exact prefixLift 4982170
  have htrace : WordTrace (prefixWord ++ tailWord_4982170) baseStart_4982170 baseEnd_4982170 := by
    simpa [prefixWord, tailWord_4982170, baseEnd_4982170] using wordTrace_append hprefix tailTrace_4982170
  have hstable : (prefixWord ++ tailWord_4982170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4982170).length < 2 ^ (prefixWord ++ tailWord_4982170).sum := by decide
  have hdescent : baseEnd_4982170 < baseStart_4982170 := by decide
  rcases family_descends (prefixWord ++ tailWord_4982170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4982197 : List Nat := [1, 3, 3, 2, 2, 1, 2, 3, 6]
def baseStart_4982197 : Nat := 118140960795 + 4982197 * 2 ^ 59
def prefixEnd_4982197 : Nat := 4983230072969 + 3 ^ 40 * 4982197 * 2
def baseEnd_4982197 : Nat := 284251308487616540558311

theorem tailTrace_4982197 : CollatzResearch.WordTrace tailWord_4982197 prefixEnd_4982197 284251308487616540558311 := by
  unfold tailWord_4982197
  simp only [CollatzResearch.WordTrace]
  refine ⟨181715653131358635349776845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121143768754239090233184563 181715653131358635349776845)
  ·
    refine ⟨68143369924259488256166317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181715653131358635349776845 68143369924259488256166317)
    ·
      refine ⟨25553763721597308096062369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68143369924259488256166317 25553763721597308096062369)
      ·
        refine ⟨19165322791197981072046777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25553763721597308096062369 19165322791197981072046777)
        ·
          refine ⟨14373992093398485804035083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19165322791197981072046777 14373992093398485804035083)
          ·
            refine ⟨21560988140097728706052625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14373992093398485804035083 21560988140097728706052625)
            ·
              refine ⟨16170741105073296529539469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21560988140097728706052625 16170741105073296529539469)
              ·
                refine ⟨6064027914402486198577301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16170741105073296529539469 6064027914402486198577301)
                ·
                  refine ⟨284251308487616540558311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6064027914402486198577301 284251308487616540558311)
                  ·
                    rfl

theorem cell23_4982197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 3, 6].length) (baseStart_4982197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4982197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4982197 prefixEnd_4982197 := by exact prefixLift 4982197
  have htrace : WordTrace (prefixWord ++ tailWord_4982197) baseStart_4982197 baseEnd_4982197 := by
    simpa [prefixWord, tailWord_4982197, baseEnd_4982197] using wordTrace_append hprefix tailTrace_4982197
  have hstable : (prefixWord ++ tailWord_4982197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4982197).length < 2 ^ (prefixWord ++ tailWord_4982197).sum := by decide
  have hdescent : baseEnd_4982197 < baseStart_4982197 := by decide
  rcases family_descends (prefixWord ++ tailWord_4982197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4982241 : List Nat := [1, 2, 3, 1, 2, 3, 2, 4, 1, 1, 3]
def baseStart_4982241 : Nat := 118140960795 + 4982241 * 2 ^ 59
def prefixEnd_4982241 : Nat := 4983230072969 + 3 ^ 40 * 4982241 * 2
def baseEnd_4982241 : Nat := 2558284369537346692874597

theorem tailTrace_4982241 : CollatzResearch.WordTrace tailWord_4982241 prefixEnd_4982241 2558284369537346692874597 := by
  unfold tailWord_4982241
  simp only [CollatzResearch.WordTrace]
  refine ⟨181717257943199230864378577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121144838628799487242919051 181717257943199230864378577)
  ·
    refine ⟨136287943457399423148283933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181717257943199230864378577 136287943457399423148283933)
    ·
      refine ⟨51107978796524783680606475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136287943457399423148283933 51107978796524783680606475)
      ·
        refine ⟨76661968194787175520909713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51107978796524783680606475 76661968194787175520909713)
        ·
          refine ⟨57496476146090381640682285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76661968194787175520909713 57496476146090381640682285)
          ·
            refine ⟨21561178554783893115255857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57496476146090381640682285 21561178554783893115255857)
            ·
              refine ⟨16170883916087919836441893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21561178554783893115255857 16170883916087919836441893)
              ·
                refine ⟨3032040734266484969332855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16170883916087919836441893 3032040734266484969332855)
                ·
                  refine ⟨4548061101399727453999283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3032040734266484969332855 4548061101399727453999283)
                  ·
                    refine ⟨6822091652099591180998925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4548061101399727453999283 6822091652099591180998925)
                    ·
                      refine ⟨2558284369537346692874597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6822091652099591180998925 2558284369537346692874597)
                      ·
                        rfl

theorem cell23_4982241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 4, 1, 1, 3].length) (baseStart_4982241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4982241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4982241 prefixEnd_4982241 := by exact prefixLift 4982241
  have htrace : WordTrace (prefixWord ++ tailWord_4982241) baseStart_4982241 baseEnd_4982241 := by
    simpa [prefixWord, tailWord_4982241, baseEnd_4982241] using wordTrace_append hprefix tailTrace_4982241
  have hstable : (prefixWord ++ tailWord_4982241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4982241).length < 2 ^ (prefixWord ++ tailWord_4982241).sum := by decide
  have hdescent : baseEnd_4982241 < baseStart_4982241 := by decide
  rcases family_descends (prefixWord ++ tailWord_4982241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4982257 : List Nat := [1, 2, 2, 2, 3, 2, 3, 1, 1, 6]
def baseStart_4982257 : Nat := 118140960795 + 4982257 * 2 ^ 59
def prefixEnd_4982257 : Nat := 4983230072969 + 3 ^ 40 * 4982257 * 2
def baseEnd_4982257 : Nat := 852764195075939543424841

theorem tailTrace_4982257 : CollatzResearch.WordTrace tailWord_4982257 prefixEnd_4982257 852764195075939543424841 := by
  unfold tailWord_4982257
  simp only [CollatzResearch.WordTrace]
  refine ⟨181717841511141265596961025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121145227674094177064640683 181717841511141265596961025)
  ·
    refine ⟨136288381133355949197720769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181717841511141265596961025 136288381133355949197720769)
    ·
      refine ⟨102216285850016961898290577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136288381133355949197720769 102216285850016961898290577)
      ·
        refine ⟨76662214387512721423717933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102216285850016961898290577 76662214387512721423717933)
        ·
          refine ⟨28748330395317270533894225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76662214387512721423717933 28748330395317270533894225)
          ·
            refine ⟨21561247796487952900420669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28748330395317270533894225 21561247796487952900420669)
            ·
              refine ⟨8085467923682982337657751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21561247796487952900420669 8085467923682982337657751)
              ·
                refine ⟨12128201885524473506486627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8085467923682982337657751 12128201885524473506486627)
                ·
                  refine ⟨18192302828286710259729941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12128201885524473506486627 18192302828286710259729941)
                  ·
                    refine ⟨852764195075939543424841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18192302828286710259729941 852764195075939543424841)
                    ·
                      rfl

theorem cell23_4982257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 1, 1, 6].length) (baseStart_4982257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4982257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4982257 prefixEnd_4982257 := by exact prefixLift 4982257
  have htrace : WordTrace (prefixWord ++ tailWord_4982257) baseStart_4982257 baseEnd_4982257 := by
    simpa [prefixWord, tailWord_4982257, baseEnd_4982257] using wordTrace_append hprefix tailTrace_4982257
  have hstable : (prefixWord ++ tailWord_4982257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4982257).length < 2 ^ (prefixWord ++ tailWord_4982257).sum := by decide
  have hdescent : baseEnd_4982257 < baseStart_4982257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4982257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4982261 : List Nat := [1, 3, 5, 1, 1, 2, 2, 2, 1, 5]
def baseStart_4982261 : Nat := 118140960795 + 4982261 * 2 ^ 59
def prefixEnd_4982261 : Nat := 4983230072969 + 3 ^ 40 * 4982261 * 2
def baseEnd_4982261 : Nat := 852764879716812204874835

theorem tailTrace_4982261 : CollatzResearch.WordTrace tailWord_4982261 prefixEnd_4982261 852764879716812204874835 := by
  unfold tailWord_4982261
  simp only [CollatzResearch.WordTrace]
  refine ⟨181717987403126774280106637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121145324935417849520071091 181717987403126774280106637)
  ·
    refine ⟨68144245276172540355039989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181717987403126774280106637 68144245276172540355039989)
    ·
      refine ⟨6388522994641175658284999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68144245276172540355039989 6388522994641175658284999)
      ·
        refine ⟨9582784491961763487427499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6388522994641175658284999 9582784491961763487427499)
        ·
          refine ⟨14374176737942645231141249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9582784491961763487427499 14374176737942645231141249)
          ·
            refine ⟨10780632553456983923355937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14374176737942645231141249 10780632553456983923355937)
            ·
              refine ⟨8085474415092737942516953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10780632553456983923355937 8085474415092737942516953)
              ·
                refine ⟨6064105811319553456887715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8085474415092737942516953 6064105811319553456887715)
                ·
                  refine ⟨9096158716979330185331573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6064105811319553456887715 9096158716979330185331573)
                  ·
                    refine ⟨852764879716812204874835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9096158716979330185331573 852764879716812204874835)
                    ·
                      rfl

theorem cell23_4982261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_4982261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4982261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4982261 prefixEnd_4982261 := by exact prefixLift 4982261
  have htrace : WordTrace (prefixWord ++ tailWord_4982261) baseStart_4982261 baseEnd_4982261 := by
    simpa [prefixWord, tailWord_4982261, baseEnd_4982261] using wordTrace_append hprefix tailTrace_4982261
  have hstable : (prefixWord ++ tailWord_4982261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4982261).length < 2 ^ (prefixWord ++ tailWord_4982261).sum := by decide
  have hdescent : baseEnd_4982261 < baseStart_4982261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4982261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4982264 : List Nat := [2, 1, 2, 1, 1, 6, 2, 2, 1, 1, 4]
def baseStart_4982264 : Nat := 118140960795 + 4982264 * 2 ^ 59
def prefixEnd_4982264 : Nat := 4983230072969 + 3 ^ 40 * 4982264 * 2
def baseEnd_4982264 : Nat := 2558296179592400102886991

theorem tailTrace_4982264 : CollatzResearch.WordTrace tailWord_4982264 prefixEnd_4982264 2558296179592400102886991 := by
  unfold tailWord_4982264
  simp only [CollatzResearch.WordTrace]
  refine ⟨90859048411057952896232923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121145397881410603861643897 90859048411057952896232923)
  ·
    refine ⟨136288572616586929344349385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90859048411057952896232923 136288572616586929344349385)
    ·
      refine ⟨102216429462440197008262039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136288572616586929344349385 102216429462440197008262039)
      ·
        refine ⟨153324644193660295512393059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102216429462440197008262039 153324644193660295512393059)
        ·
          refine ⟨229986966290490443268589589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153324644193660295512393059 229986966290490443268589589)
          ·
            refine ⟨10780639044866739528215137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 229986966290490443268589589 10780639044866739528215137)
            ·
              refine ⟨8085479283650054646161353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10780639044866739528215137 8085479283650054646161353)
              ·
                refine ⟨6064109462737540984621015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8085479283650054646161353 6064109462737540984621015)
                ·
                  refine ⟨9096164194106311476931523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6064109462737540984621015 9096164194106311476931523)
                  ·
                    refine ⟨13644246291159467215397285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9096164194106311476931523 13644246291159467215397285)
                    ·
                      refine ⟨2558296179592400102886991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13644246291159467215397285 2558296179592400102886991)
                      ·
                        rfl

theorem cell23_4982264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 2, 1, 1, 4].length) (baseStart_4982264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4982264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4982264 prefixEnd_4982264 := by exact prefixLift 4982264
  have htrace : WordTrace (prefixWord ++ tailWord_4982264) baseStart_4982264 baseEnd_4982264 := by
    simpa [prefixWord, tailWord_4982264, baseEnd_4982264] using wordTrace_append hprefix tailTrace_4982264
  have hstable : (prefixWord ++ tailWord_4982264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4982264).length < 2 ^ (prefixWord ++ tailWord_4982264).sum := by decide
  have hdescent : baseEnd_4982264 < baseStart_4982264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4982264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4982284 : List Nat := [2, 2, 1, 2, 5, 1, 2, 1, 1, 1, 5]
def baseStart_4982284 : Nat := 118140960795 + 4982284 * 2 ^ 59
def prefixEnd_4982284 : Nat := 4983230072969 + 3 ^ 40 * 4982284 * 2
def baseEnd_4982284 : Nat := 2558306449205490024636899

theorem tailTrace_4982284 : CollatzResearch.WordTrace tailWord_4982284 prefixEnd_4982284 2558306449205490024636899 := by
  unfold tailWord_4982284
  simp only [CollatzResearch.WordTrace]
  refine ⟨90859413141021724604096953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121145884188028966138795937 90859413141021724604096953)
  ·
    refine ⟨68144559855766293453072715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90859413141021724604096953 68144559855766293453072715)
    ·
      refine ⟨102216839783649440179609073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68144559855766293453072715 102216839783649440179609073)
      ·
        refine ⟨76662629837737080134706805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102216839783649440179609073 76662629837737080134706805)
        ·
          refine ⟨7187121547287851262628763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76662629837737080134706805 7187121547287851262628763)
          ·
            refine ⟨10780682320931776893943145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7187121547287851262628763 10780682320931776893943145)
            ·
              refine ⟨8085511740698832670457359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10780682320931776893943145 8085511740698832670457359)
              ·
                refine ⟨12128267611048249005686039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8085511740698832670457359 12128267611048249005686039)
                ·
                  refine ⟨18192401416572373508529059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12128267611048249005686039 18192401416572373508529059)
                  ·
                    refine ⟨27288602124858560262793589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18192401416572373508529059 27288602124858560262793589)
                    ·
                      refine ⟨2558306449205490024636899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27288602124858560262793589 2558306449205490024636899)
                      ·
                        rfl

theorem cell23_4982284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 1, 1, 1, 5].length) (baseStart_4982284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4982284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4982284 prefixEnd_4982284 := by exact prefixLift 4982284
  have htrace : WordTrace (prefixWord ++ tailWord_4982284) baseStart_4982284 baseEnd_4982284 := by
    simpa [prefixWord, tailWord_4982284, baseEnd_4982284] using wordTrace_append hprefix tailTrace_4982284
  have hstable : (prefixWord ++ tailWord_4982284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4982284).length < 2 ^ (prefixWord ++ tailWord_4982284).sum := by decide
  have hdescent : baseEnd_4982284 < baseStart_4982284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4982284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4982285 : List Nat := [1, 7, 1, 1, 2, 1, 1, 2, 2, 3, 2]
def baseStart_4982285 : Nat := 118140960795 + 4982285 * 2 ^ 59
def prefixEnd_4982285 : Nat := 4983230072969 + 3 ^ 40 * 4982285 * 2
def baseEnd_4982285 : Nat := 2558306962686144520724395

theorem tailTrace_4982285 : CollatzResearch.WordTrace tailWord_4982285 prefixEnd_4982285 2558306962686144520724395 := by
  unfold tailWord_4982285
  simp only [CollatzResearch.WordTrace]
  refine ⟨181718862755039826378980309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121145908503359884252653539 181718862755039826378980309)
  ·
    refine ⟨4259035845821245930757351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 181718862755039826378980309 4259035845821245930757351)
    ·
      refine ⟨6388553768731868896136027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4259035845821245930757351 6388553768731868896136027)
      ·
        refine ⟨9582830653097803344204041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6388553768731868896136027 9582830653097803344204041)
        ·
          refine ⟨7187122989823352508153031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9582830653097803344204041 7187122989823352508153031)
          ·
            refine ⟨10780684484735028762229547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7187122989823352508153031 10780684484735028762229547)
            ·
              refine ⟨16171026727102543143344321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10780684484735028762229547 16171026727102543143344321)
              ·
                refine ⟨12128270045326907357508241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16171026727102543143344321 12128270045326907357508241)
                ·
                  refine ⟨9096202533995180518131181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12128270045326907357508241 9096202533995180518131181)
                  ·
                    refine ⟨3411075950248192694299193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9096202533995180518131181 3411075950248192694299193)
                    ·
                      refine ⟨2558306962686144520724395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3411075950248192694299193 2558306962686144520724395)
                      ·
                        rfl

theorem cell23_4982285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_4982285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4982285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4982285 prefixEnd_4982285 := by exact prefixLift 4982285
  have htrace : WordTrace (prefixWord ++ tailWord_4982285) baseStart_4982285 baseEnd_4982285 := by
    simpa [prefixWord, tailWord_4982285, baseEnd_4982285] using wordTrace_append hprefix tailTrace_4982285
  have hstable : (prefixWord ++ tailWord_4982285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4982285).length < 2 ^ (prefixWord ++ tailWord_4982285).sum := by decide
  have hdescent : baseEnd_4982285 < baseStart_4982285 := by decide
  rcases family_descends (prefixWord ++ tailWord_4982285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4982292 : List Nat := [2, 4, 3, 1, 2, 1, 3, 2, 1, 1, 3]
def baseStart_4982292 : Nat := 118140960795 + 4982292 * 2 ^ 59
def prefixEnd_4982292 : Nat := 4983230072969 + 3 ^ 40 * 4982292 * 2
def baseEnd_4982292 : Nat := 2558310557050725993336863

theorem tailTrace_4982292 : CollatzResearch.WordTrace tailWord_4982292 prefixEnd_4982292 2558310557050725993336863 := by
  unfold tailWord_4982292
  simp only [CollatzResearch.WordTrace]
  refine ⟨90859559033007233287242565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121146078710676311049656753 90859559033007233287242565)
  ·
    refine ⟨17036167318688856241357981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90859559033007233287242565 17036167318688856241357981)
    ·
      refine ⟨6388562744508321090509243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17036167318688856241357981 6388562744508321090509243)
      ·
        refine ⟨9582844116762481635763865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6388562744508321090509243 9582844116762481635763865)
        ·
          refine ⟨7187133087571861226822899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9582844116762481635763865 7187133087571861226822899)
          ·
            refine ⟨10780699631357791840234349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7187133087571861226822899 10780699631357791840234349)
            ·
              refine ⟨4042762361759171940087881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10780699631357791840234349 4042762361759171940087881)
              ·
                refine ⟨3032071771319378955065911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4042762361759171940087881 3032071771319378955065911)
                ·
                  refine ⟨4548107656979068432598867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3032071771319378955065911 4548107656979068432598867)
                  ·
                    refine ⟨6822161485468602648898301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4548107656979068432598867 6822161485468602648898301)
                    ·
                      refine ⟨2558310557050725993336863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6822161485468602648898301 2558310557050725993336863)
                      ·
                        rfl

theorem cell23_4982292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_4982292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4982292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4982292 prefixEnd_4982292 := by exact prefixLift 4982292
  have htrace : WordTrace (prefixWord ++ tailWord_4982292) baseStart_4982292 baseEnd_4982292 := by
    simpa [prefixWord, tailWord_4982292, baseEnd_4982292] using wordTrace_append hprefix tailTrace_4982292
  have hstable : (prefixWord ++ tailWord_4982292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4982292).length < 2 ^ (prefixWord ++ tailWord_4982292).sum := by decide
  have hdescent : baseEnd_4982292 < baseStart_4982292 := by decide
  rcases family_descends (prefixWord ++ tailWord_4982292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4982314 : List Nat := [3, 1, 4, 1, 1, 1, 2, 3, 1, 3, 3]
def baseStart_4982314 : Nat := 118140960795 + 4982314 * 2 ^ 59
def prefixEnd_4982314 : Nat := 4983230072969 + 3 ^ 40 * 4982314 * 2
def baseEnd_4982314 : Nat := 2558321853625124907261761

theorem tailTrace_4982314 : CollatzResearch.WordTrace tailWord_4982314 prefixEnd_4982314 2558321853625124907261761 := by
  unfold tailWord_4982314
  simp only [CollatzResearch.WordTrace]
  refine ⟨45429980117983691082946499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121146613647956509554523997 45429980117983691082946499)
  ·
    refine ⟨68144970176975536624419749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45429980117983691082946499 68144970176975536624419749)
    ·
      refine ⟨12777181908182913117078703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68144970176975536624419749 12777181908182913117078703)
      ·
        refine ⟨19165772862274369675618055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12777181908182913117078703 19165772862274369675618055)
        ·
          refine ⟨28748659293411554513427083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19165772862274369675618055 28748659293411554513427083)
          ·
            refine ⟨43122988940117331770140625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28748659293411554513427083 43122988940117331770140625)
            ·
              refine ⟨32342241705087998827605469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43122988940117331770140625 32342241705087998827605469)
              ·
                refine ⟨12128340639407999560352051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32342241705087998827605469 12128340639407999560352051)
                ·
                  refine ⟨18192510959111999340528077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12128340639407999560352051 18192510959111999340528077)
                  ·
                    refine ⟨6822191609666999752698029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18192510959111999340528077 6822191609666999752698029)
                    ·
                      refine ⟨2558321853625124907261761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6822191609666999752698029 2558321853625124907261761)
                      ·
                        rfl

theorem cell23_4982314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_4982314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4982314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4982314 prefixEnd_4982314 := by exact prefixLift 4982314
  have htrace : WordTrace (prefixWord ++ tailWord_4982314) baseStart_4982314 baseEnd_4982314 := by
    simpa [prefixWord, tailWord_4982314, baseEnd_4982314] using wordTrace_append hprefix tailTrace_4982314
  have hstable : (prefixWord ++ tailWord_4982314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4982314).length < 2 ^ (prefixWord ++ tailWord_4982314).sum := by decide
  have hdescent : baseEnd_4982314 < baseStart_4982314 := by decide
  rcases family_descends (prefixWord ++ tailWord_4982314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4982318 : List Nat := [4, 1, 3, 1, 2, 3, 1, 2, 1, 2, 3]
def baseStart_4982318 : Nat := 118140960795 + 4982318 * 2 ^ 59
def prefixEnd_4982318 : Nat := 4983230072969 + 3 ^ 40 * 4982318 * 2
def baseEnd_4982318 : Nat := 2558323907547742891611743

theorem tailTrace_4982318 : CollatzResearch.WordTrace tailWord_4982318 prefixEnd_4982318 2558323907547742891611743 := by
  unfold tailWord_4982318
  simp only [CollatzResearch.WordTrace]
  refine ⟨22715008295490034126866451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121146710909280182009954405 22715008295490034126866451)
  ·
    refine ⟨34072512443235051190299677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22715008295490034126866451 34072512443235051190299677)
    ·
      refine ⟨12777192166213144196362379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34072512443235051190299677 12777192166213144196362379)
      ·
        refine ⟨19165788249319716294543569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12777192166213144196362379 19165788249319716294543569)
        ·
          refine ⟨14374341186989787220907677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19165788249319716294543569 14374341186989787220907677)
          ·
            refine ⟨5390377945121170207840379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14374341186989787220907677 5390377945121170207840379)
            ·
              refine ⟨8085566917681755311760569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5390377945121170207840379 8085566917681755311760569)
              ·
                refine ⟨6064175188261316483820427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8085566917681755311760569 6064175188261316483820427)
                ·
                  refine ⟨9096262782391974725730641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6064175188261316483820427 9096262782391974725730641)
                  ·
                    refine ⟨6822197086793981044297981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9096262782391974725730641 6822197086793981044297981)
                    ·
                      refine ⟨2558323907547742891611743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6822197086793981044297981 2558323907547742891611743)
                      ·
                        rfl

theorem cell23_4982318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_4982318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4982318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4982318 prefixEnd_4982318 := by exact prefixLift 4982318
  have htrace : WordTrace (prefixWord ++ tailWord_4982318) baseStart_4982318 baseEnd_4982318 := by
    simpa [prefixWord, tailWord_4982318, baseEnd_4982318] using wordTrace_append hprefix tailTrace_4982318
  have hstable : (prefixWord ++ tailWord_4982318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4982318).length < 2 ^ (prefixWord ++ tailWord_4982318).sum := by decide
  have hdescent : baseEnd_4982318 < baseStart_4982318 := by decide
  rcases family_descends (prefixWord ++ tailWord_4982318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4982320 : List Nat := [2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 8]
def baseStart_4982320 : Nat := 118140960795 + 4982320 * 2 ^ 59
def prefixEnd_4982320 : Nat := 4983230072969 + 3 ^ 40 * 4982320 * 2
def baseEnd_4982320 : Nat := 2558324934509051883786733

theorem tailTrace_4982320 : CollatzResearch.WordTrace tailWord_4982320 prefixEnd_4982320 2558324934509051883786733 := by
  unfold tailWord_4982320
  simp only [CollatzResearch.WordTrace]
  refine ⟨90860069654956513678252207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121146759539942018237669609 90860069654956513678252207)
  ·
    refine ⟨136290104482434770517378311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90860069654956513678252207 136290104482434770517378311)
    ·
      refine ⟨204435156723652155776067467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136290104482434770517378311 204435156723652155776067467)
      ·
        refine ⟨306652735085478233664101201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204435156723652155776067467 306652735085478233664101201)
        ·
          refine ⟨229989551314108675248075901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 306652735085478233664101201 229989551314108675248075901)
          ·
            refine ⟨86246081742790753218028463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 229989551314108675248075901 86246081742790753218028463)
            ·
              refine ⟨129369122614186129827042695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86246081742790753218028463 129369122614186129827042695)
              ·
                refine ⟨194053683921279194740564043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129369122614186129827042695 194053683921279194740564043)
                ·
                  refine ⟨291080525881918792110846065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 194053683921279194740564043 291080525881918792110846065)
                  ·
                    refine ⟨218310394411439094083134549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 291080525881918792110846065 218310394411439094083134549)
                    ·
                      refine ⟨2558324934509051883786733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 218310394411439094083134549 2558324934509051883786733)
                      ·
                        rfl

theorem cell23_4982320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 8].length) (baseStart_4982320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4982320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4982320 prefixEnd_4982320 := by exact prefixLift 4982320
  have htrace : WordTrace (prefixWord ++ tailWord_4982320) baseStart_4982320 baseEnd_4982320 := by
    simpa [prefixWord, tailWord_4982320, baseEnd_4982320] using wordTrace_append hprefix tailTrace_4982320
  have hstable : (prefixWord ++ tailWord_4982320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4982320).length < 2 ^ (prefixWord ++ tailWord_4982320).sum := by decide
  have hdescent : baseEnd_4982320 < baseStart_4982320 := by decide
  rcases family_descends (prefixWord ++ tailWord_4982320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4982349 : List Nat := [1, 6, 1, 1, 3, 2, 2, 2, 1, 2, 2]
def baseStart_4982349 : Nat := 118140960795 + 4982349 * 2 ^ 59
def prefixEnd_4982349 : Nat := 4983230072969 + 3 ^ 40 * 4982349 * 2
def baseEnd_4982349 : Nat := 2558339825448032270324101

theorem tailTrace_4982349 : CollatzResearch.WordTrace tailWord_4982349 prefixEnd_4982349 2558339825448032270324101 := by
  unfold tailWord_4982349
  simp only [CollatzResearch.WordTrace]
  refine ⟨181721197026807965309310101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121147464684538643539540067 181721197026807965309310101)
  ·
    refine ⟨8518181110631623373873911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 181721197026807965309310101 8518181110631623373873911)
    ·
      refine ⟨12777271665947435060810867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8518181110631623373873911 12777271665947435060810867)
      ·
        refine ⟨19165907498921152591216301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12777271665947435060810867 19165907498921152591216301)
        ·
          refine ⟨7187215312095432221706113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19165907498921152591216301 7187215312095432221706113)
          ·
            refine ⟨5390411484071574166279585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7187215312095432221706113 5390411484071574166279585)
            ·
              refine ⟨4042808613053680624709689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5390411484071574166279585 4042808613053680624709689)
              ·
                refine ⟨3032106459790260468532267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4042808613053680624709689 3032106459790260468532267)
                ·
                  refine ⟨4548159689685390702798401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3032106459790260468532267 4548159689685390702798401)
                  ·
                    refine ⟨3411119767264043027098801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4548159689685390702798401 3411119767264043027098801)
                    ·
                      refine ⟨2558339825448032270324101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3411119767264043027098801 2558339825448032270324101)
                      ·
                        rfl

theorem cell23_4982349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_4982349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4982349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4982349 prefixEnd_4982349 := by exact prefixLift 4982349
  have htrace : WordTrace (prefixWord ++ tailWord_4982349) baseStart_4982349 baseEnd_4982349 := by
    simpa [prefixWord, tailWord_4982349, baseEnd_4982349] using wordTrace_append hprefix tailTrace_4982349
  have hstable : (prefixWord ++ tailWord_4982349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4982349).length < 2 ^ (prefixWord ++ tailWord_4982349).sum := by decide
  have hdescent : baseEnd_4982349 < baseStart_4982349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4982349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4982364 : List Nat := [2, 2, 4, 1, 2, 2, 1, 1, 2, 6]
def baseStart_4982364 : Nat := 118140960795 + 4982364 * 2 ^ 59
def prefixEnd_4982364 : Nat := 4983230072969 + 3 ^ 40 * 4982364 * 2
def baseEnd_4982364 : Nat := 852782509219283237212177

theorem tailTrace_4982364 : CollatzResearch.WordTrace tailWord_4982364 prefixEnd_4982364 852782509219283237212177 := by
  unfold tailWord_4982364
  simp only [CollatzResearch.WordTrace]
  refine ⟨90860872060876811435553073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121147829414502415247404097 90860872060876811435553073)
  ·
    refine ⟨68145654045657608576664805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90860872060876811435553073 68145654045657608576664805)
    ·
      refine ⟨12777310133560801608124651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68145654045657608576664805 12777310133560801608124651)
      ·
        refine ⟨19165965200341202412186977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12777310133560801608124651 19165965200341202412186977)
        ·
          refine ⟨14374473900255901809140233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19165965200341202412186977 14374473900255901809140233)
          ·
            refine ⟨10780855425191926356855175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14374473900255901809140233 10780855425191926356855175)
            ·
              refine ⟨16171283137787889535282763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10780855425191926356855175 16171283137787889535282763)
              ·
                refine ⟨24256924706681834302924145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16171283137787889535282763 24256924706681834302924145)
                ·
                  refine ⟨18192693530011375727193109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24256924706681834302924145 18192693530011375727193109)
                  ·
                    refine ⟨852782509219283237212177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18192693530011375727193109 852782509219283237212177)
                    ·
                      rfl

theorem cell23_4982364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_4982364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4982364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4982364 prefixEnd_4982364 := by exact prefixLift 4982364
  have htrace : WordTrace (prefixWord ++ tailWord_4982364) baseStart_4982364 baseEnd_4982364 := by
    simpa [prefixWord, tailWord_4982364, baseEnd_4982364] using wordTrace_append hprefix tailTrace_4982364
  have hstable : (prefixWord ++ tailWord_4982364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4982364).length < 2 ^ (prefixWord ++ tailWord_4982364).sum := by decide
  have hdescent : baseEnd_4982364 < baseStart_4982364 := by decide
  rcases family_descends (prefixWord ++ tailWord_4982364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4982371 : List Nat := [1, 1, 1, 5, 1, 4, 2, 1, 1, 4, 2]
def baseStart_4982371 : Nat := 118140960795 + 4982371 * 2 ^ 59
def prefixEnd_4982371 : Nat := 4983230072969 + 3 ^ 40 * 4982371 * 2
def baseEnd_4982371 : Nat := 2558351122022431184248999

theorem tailTrace_4982371 : CollatzResearch.WordTrace tailWord_4982371 prefixEnd_4982371 2558351122022431184248999 := by
  unfold tailWord_4982371
  simp only [CollatzResearch.WordTrace]
  refine ⟨181721999432728263066610967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121147999621818842044407311 181721999432728263066610967)
  ·
    refine ⟨272582999149092394599916451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181721999432728263066610967 272582999149092394599916451)
    ·
      refine ⟨408874498723638591899874677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272582999149092394599916451 408874498723638591899874677)
      ·
        refine ⟨38331984255341117990613251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 408874498723638591899874677 38331984255341117990613251)
        ·
          refine ⟨57497976383011676985919877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38331984255341117990613251 57497976383011676985919877)
          ·
            refine ⟨10780870571814689434859977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57497976383011676985919877 10780870571814689434859977)
            ·
              refine ⟨8085652928861017076144983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10780870571814689434859977 8085652928861017076144983)
              ·
                refine ⟨12128479393291525614217475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8085652928861017076144983 12128479393291525614217475)
                ·
                  refine ⟨18192719089937288421326213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12128479393291525614217475 18192719089937288421326213)
                  ·
                    refine ⟨3411134829363241578998665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18192719089937288421326213 3411134829363241578998665)
                    ·
                      refine ⟨2558351122022431184248999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3411134829363241578998665 2558351122022431184248999)
                      ·
                        rfl

theorem cell23_4982371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 1, 1, 4, 2].length) (baseStart_4982371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4982371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4982371 prefixEnd_4982371 := by exact prefixLift 4982371
  have htrace : WordTrace (prefixWord ++ tailWord_4982371) baseStart_4982371 baseEnd_4982371 := by
    simpa [prefixWord, tailWord_4982371, baseEnd_4982371] using wordTrace_append hprefix tailTrace_4982371
  have hstable : (prefixWord ++ tailWord_4982371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4982371).length < 2 ^ (prefixWord ++ tailWord_4982371).sum := by decide
  have hdescent : baseEnd_4982371 < baseStart_4982371 := by decide
  rcases family_descends (prefixWord ++ tailWord_4982371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4982457 : List Nat := [1, 2, 1, 4, 1, 1, 2, 1, 1, 3, 6]
def baseStart_4982457 : Nat := 118140960795 + 4982457 * 2 ^ 59
def prefixEnd_4982457 : Nat := 4983230072969 + 3 ^ 40 * 4982457 * 2
def baseEnd_4982457 : Nat := 2558395281358717847773603

theorem tailTrace_4982457 : CollatzResearch.WordTrace tailWord_4982457 prefixEnd_4982457 2558395281358717847773603 := by
  unfold tailWord_4982457
  simp only [CollatzResearch.WordTrace]
  refine ⟨181725136110416699754241625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121150090740277799836161083 181725136110416699754241625)
  ·
    refine ⟨136293852082812524815681219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181725136110416699754241625 136293852082812524815681219)
    ·
      refine ⟨204440778124218787223521829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136293852082812524815681219 204440778124218787223521829)
      ·
        refine ⟨38332645898291022604410343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 204440778124218787223521829 38332645898291022604410343)
        ·
          refine ⟨57498968847436533906615515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38332645898291022604410343 57498968847436533906615515)
          ·
            refine ⟨86248453271154800859923273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57498968847436533906615515 86248453271154800859923273)
            ·
              refine ⟨64686339953366100644942455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86248453271154800859923273 64686339953366100644942455)
              ·
                refine ⟨97029509930049150967413683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64686339953366100644942455 97029509930049150967413683)
                ·
                  refine ⟨145544264895073726451120525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97029509930049150967413683 145544264895073726451120525)
                  ·
                    refine ⟨54579099335652647419170197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 145544264895073726451120525 54579099335652647419170197)
                    ·
                      refine ⟨2558395281358717847773603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54579099335652647419170197 2558395281358717847773603)
                      ·
                        rfl

theorem cell23_4982457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_4982457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4982457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4982457 prefixEnd_4982457 := by exact prefixLift 4982457
  have htrace : WordTrace (prefixWord ++ tailWord_4982457) baseStart_4982457 baseEnd_4982457 := by
    simpa [prefixWord, tailWord_4982457, baseEnd_4982457] using wordTrace_append hprefix tailTrace_4982457
  have hstable : (prefixWord ++ tailWord_4982457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4982457).length < 2 ^ (prefixWord ++ tailWord_4982457).sum := by decide
  have hdescent : baseEnd_4982457 < baseStart_4982457 := by decide
  rcases family_descends (prefixWord ++ tailWord_4982457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4982528 : List Nat := [2, 1, 1, 2, 1, 1, 2, 8, 1, 1, 3]
def baseStart_4982528 : Nat := 118140960795 + 4982528 * 2 ^ 59
def prefixEnd_4982528 : Nat := 4983230072969 + 3 ^ 40 * 4982528 * 2
def baseEnd_4982528 : Nat := 2558431738485187069985777

theorem tailTrace_4982528 : CollatzResearch.WordTrace tailWord_4982528 prefixEnd_4982528 2558431738485187069985777 := by
  unfold tailWord_4982528
  simp only [CollatzResearch.WordTrace]
  refine ⟨90863862846579739440038119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121151817128772985920050825 90863862846579739440038119)
  ·
    refine ⟨136295794269869609160057179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90863862846579739440038119 136295794269869609160057179)
    ·
      refine ⟨204443691404804413740085769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136295794269869609160057179 204443691404804413740085769)
      ·
        refine ⟨153332768553603310305064327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204443691404804413740085769 153332768553603310305064327)
        ·
          refine ⟨229999152830404965457596491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153332768553603310305064327 229999152830404965457596491)
          ·
            refine ⟨344998729245607448186394737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229999152830404965457596491 344998729245607448186394737)
            ·
              refine ⟨258749046934205586139796053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 344998729245607448186394737 258749046934205586139796053)
              ·
                refine ⟨3032215393760221712575735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 258749046934205586139796053 3032215393760221712575735)
                ·
                  refine ⟨4548323090640332568863603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3032215393760221712575735 4548323090640332568863603)
                  ·
                    refine ⟨6822484635960498853295405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4548323090640332568863603 6822484635960498853295405)
                    ·
                      refine ⟨2558431738485187069985777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6822484635960498853295405 2558431738485187069985777)
                      ·
                        rfl

theorem cell23_4982528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 8, 1, 1, 3].length) (baseStart_4982528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4982528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4982528 prefixEnd_4982528 := by exact prefixLift 4982528
  have htrace : WordTrace (prefixWord ++ tailWord_4982528) baseStart_4982528 baseEnd_4982528 := by
    simpa [prefixWord, tailWord_4982528, baseEnd_4982528] using wordTrace_append hprefix tailTrace_4982528
  have hstable : (prefixWord ++ tailWord_4982528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4982528).length < 2 ^ (prefixWord ++ tailWord_4982528).sum := by decide
  have hdescent : baseEnd_4982528 < baseStart_4982528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4982528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4982551 : List Nat := [1, 1, 3, 4, 2, 1, 2, 1, 3, 1, 4]
def baseStart_4982551 : Nat := 118140960795 + 4982551 * 2 ^ 59
def prefixEnd_4982551 : Nat := 4983230072969 + 3 ^ 40 * 4982551 * 2
def baseEnd_4982551 : Nat := 2558443548540240479998171

theorem tailTrace_4982551 : CollatzResearch.WordTrace tailWord_4982551 prefixEnd_4982551 2558443548540240479998171 := by
  unfold tailWord_4982551
  simp only [CollatzResearch.WordTrace]
  refine ⟨181728564572076153808163507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121152376381384102538775671 181728564572076153808163507)
  ·
    refine ⟨272592846858114230712245261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181728564572076153808163507 272592846858114230712245261)
    ·
      refine ⟨102222317571792836517091973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 272592846858114230712245261 102222317571792836517091973)
      ·
        refine ⟨19166684544711156846954745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102222317571792836517091973 19166684544711156846954745)
        ·
          refine ⟨14375013408533367635216059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19166684544711156846954745 14375013408533367635216059)
          ·
            refine ⟨21562520112800051452824089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14375013408533367635216059 21562520112800051452824089)
            ·
              refine ⟨16171890084600038589618067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21562520112800051452824089 16171890084600038589618067)
              ·
                refine ⟨24257835126900057884427101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16171890084600038589618067 24257835126900057884427101)
                ·
                  refine ⟨9096688172587521706660163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24257835126900057884427101 9096688172587521706660163)
                  ·
                    refine ⟨13645032258881282559990245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9096688172587521706660163 13645032258881282559990245)
                    ·
                      refine ⟨2558443548540240479998171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13645032258881282559990245 2558443548540240479998171)
                      ·
                        rfl

theorem cell23_4982551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_4982551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4982551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4982551 prefixEnd_4982551 := by exact prefixLift 4982551
  have htrace : WordTrace (prefixWord ++ tailWord_4982551) baseStart_4982551 baseEnd_4982551 := by
    simpa [prefixWord, tailWord_4982551, baseEnd_4982551] using wordTrace_append hprefix tailTrace_4982551
  have hstable : (prefixWord ++ tailWord_4982551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4982551).length < 2 ^ (prefixWord ++ tailWord_4982551).sum := by decide
  have hdescent : baseEnd_4982551 < baseStart_4982551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4982551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4982568 : List Nat := [2, 1, 5, 1, 1, 3, 1, 3, 1, 1, 4]
def baseStart_4982568 : Nat := 118140960795 + 4982568 * 2 ^ 59
def prefixEnd_4982568 : Nat := 4983230072969 + 3 ^ 40 * 4982568 * 2
def baseEnd_4982568 : Nat := 2558452277711366913485593

theorem tailTrace_4982568 : CollatzResearch.WordTrace tailWord_4982568 prefixEnd_4982568 2558452277711366913485593 := by
  unfold tailWord_4982568
  simp only [CollatzResearch.WordTrace]
  refine ⟨90864592306507282855766179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121152789742009710474354905 90864592306507282855766179)
  ·
    refine ⟨136296888459760924283649269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90864592306507282855766179 136296888459760924283649269)
    ·
      refine ⟨12777833293102586651592119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 136296888459760924283649269 12777833293102586651592119)
      ·
        refine ⟨19166749939653879977388179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12777833293102586651592119 19166749939653879977388179)
        ·
          refine ⟨28750124909480819966082269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19166749939653879977388179 28750124909480819966082269)
          ·
            refine ⟨10781296841055307487280851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28750124909480819966082269 10781296841055307487280851)
            ·
              refine ⟨16171945261582961230921277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10781296841055307487280851 16171945261582961230921277)
              ·
                refine ⟨6064479473093610461595479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16171945261582961230921277 6064479473093610461595479)
                ·
                  refine ⟨9096719209640415692393219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6064479473093610461595479 9096719209640415692393219)
                  ·
                    refine ⟨13645078814460623538589829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9096719209640415692393219 13645078814460623538589829)
                    ·
                      refine ⟨2558452277711366913485593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13645078814460623538589829 2558452277711366913485593)
                      ·
                        rfl

theorem cell23_4982568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_4982568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4982568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4982568 prefixEnd_4982568 := by exact prefixLift 4982568
  have htrace : WordTrace (prefixWord ++ tailWord_4982568) baseStart_4982568 baseEnd_4982568 := by
    simpa [prefixWord, tailWord_4982568, baseEnd_4982568] using wordTrace_append hprefix tailTrace_4982568
  have hstable : (prefixWord ++ tailWord_4982568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4982568).length < 2 ^ (prefixWord ++ tailWord_4982568).sum := by decide
  have hdescent : baseEnd_4982568 < baseStart_4982568 := by decide
  rcases family_descends (prefixWord ++ tailWord_4982568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4982578 : List Nat := [3, 2, 1, 1, 3, 2, 3, 2, 2, 4]
def baseStart_4982578 : Nat := 118140960795 + 4982578 * 2 ^ 59
def prefixEnd_4982578 : Nat := 4983230072969 + 3 ^ 40 * 4982578 * 2
def baseEnd_4982578 : Nat := 852819137505970624786849

theorem tailTrace_4982578 : CollatzResearch.WordTrace tailWord_4982578 prefixEnd_4982578 852819137505970624786849 := by
  unfold tailWord_4982578
  simp only [CollatzResearch.WordTrace]
  refine ⟨45432387335744584354849097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121153032895318891612930925 45432387335744584354849097)
  ·
    refine ⟨34074290501808438266136823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45432387335744584354849097 34074290501808438266136823)
    ·
      refine ⟨51111435752712657399205235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34074290501808438266136823 51111435752712657399205235)
      ·
        refine ⟨76667153629068986098807853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51111435752712657399205235 76667153629068986098807853)
        ·
          refine ⟨28750182610900869787052945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76667153629068986098807853 28750182610900869787052945)
          ·
            refine ⟨21562636958175652340289709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28750182610900869787052945 21562636958175652340289709)
            ·
              refine ⟨8085988859315869627608641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21562636958175652340289709 8085988859315869627608641)
              ·
                refine ⟨6064491644486902220706481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8085988859315869627608641 6064491644486902220706481)
                ·
                  refine ⟨4548368733365176665529861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6064491644486902220706481 4548368733365176665529861)
                  ·
                    refine ⟨852819137505970624786849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4548368733365176665529861 852819137505970624786849)
                    ·
                      rfl

theorem cell23_4982578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 2, 2, 4].length) (baseStart_4982578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4982578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4982578 prefixEnd_4982578 := by exact prefixLift 4982578
  have htrace : WordTrace (prefixWord ++ tailWord_4982578) baseStart_4982578 baseEnd_4982578 := by
    simpa [prefixWord, tailWord_4982578, baseEnd_4982578] using wordTrace_append hprefix tailTrace_4982578
  have hstable : (prefixWord ++ tailWord_4982578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4982578).length < 2 ^ (prefixWord ++ tailWord_4982578).sum := by decide
  have hdescent : baseEnd_4982578 < baseStart_4982578 := by decide
  rcases family_descends (prefixWord ++ tailWord_4982578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4982605 : List Nat := [1, 6, 1, 2, 1, 1, 1, 4, 1, 2, 3]
def baseStart_4982605 : Nat := 118140960795 + 4982605 * 2 ^ 59
def prefixEnd_4982605 : Nat := 4983230072969 + 3 ^ 40 * 4982605 * 2
def baseEnd_4982605 : Nat := 2558471276495583268722923

theorem tailTrace_4982605 : CollatzResearch.WordTrace tailWord_4982605 prefixEnd_4982605 2558471276495583268722923 := by
  unfold tailWord_4982605
  simp only [CollatzResearch.WordTrace]
  refine ⟨181730534113880521030629269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121153689409253680687086179 181730534113880521030629269)
  ·
    refine ⟨8518618786588149423310747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 181730534113880521030629269 8518618786588149423310747)
    ·
      refine ⟨12777928179882224134966121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8518618786588149423310747 12777928179882224134966121)
      ·
        refine ⟨9583446134911668101224591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12777928179882224134966121 9583446134911668101224591)
        ·
          refine ⟨14375169202367502151836887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9583446134911668101224591 14375169202367502151836887)
          ·
            refine ⟨21562753803551253227755331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14375169202367502151836887 21562753803551253227755331)
            ·
              refine ⟨32344130705326879841632997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21562753803551253227755331 32344130705326879841632997)
              ·
                refine ⟨6064524507248789970306187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32344130705326879841632997 6064524507248789970306187)
                ·
                  refine ⟨9096786760873184955459281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6064524507248789970306187 9096786760873184955459281)
                  ·
                    refine ⟨6822590070654888716594461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9096786760873184955459281 6822590070654888716594461)
                    ·
                      refine ⟨2558471276495583268722923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6822590070654888716594461 2558471276495583268722923)
                      ·
                        rfl

theorem cell23_4982605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_4982605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4982605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4982605 prefixEnd_4982605 := by exact prefixLift 4982605
  have htrace : WordTrace (prefixWord ++ tailWord_4982605) baseStart_4982605 baseEnd_4982605 := by
    simpa [prefixWord, tailWord_4982605, baseEnd_4982605] using wordTrace_append hprefix tailTrace_4982605
  have hstable : (prefixWord ++ tailWord_4982605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4982605).length < 2 ^ (prefixWord ++ tailWord_4982605).sum := by decide
  have hdescent : baseEnd_4982605 < baseStart_4982605 := by decide
  rcases family_descends (prefixWord ++ tailWord_4982605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4982691 : List Nat := [1, 1, 1, 4, 1, 2, 1, 4, 2, 3, 3]
def baseStart_4982691 : Nat := 118140960795 + 4982691 * 2 ^ 59
def prefixEnd_4982691 : Nat := 4983230072969 + 3 ^ 40 * 4982691 * 2
def baseEnd_4982691 : Nat := 2558515435831869932247527

theorem tailTrace_4982691 : CollatzResearch.WordTrace tailWord_4982691 prefixEnd_4982691 2558515435831869932247527 := by
  unfold tailWord_4982691
  simp only [CollatzResearch.WordTrace]
  refine ⟨181733670791568957718259927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121155780527712638478839951 181733670791568957718259927)
  ·
    refine ⟨272600506187353436577389891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181733670791568957718259927 272600506187353436577389891)
    ·
      refine ⟨408900759281030154866084837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272600506187353436577389891 408900759281030154866084837)
      ·
        refine ⟨76668892365193154037390907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 408900759281030154866084837 76668892365193154037390907)
        ·
          refine ⟨115003338547789731056086361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76668892365193154037390907 115003338547789731056086361)
          ·
            refine ⟨86252503910842298292064771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115003338547789731056086361 86252503910842298292064771)
            ·
              refine ⟨129378755866263447438097157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86252503910842298292064771 129378755866263447438097157)
              ·
                refine ⟨24258516724924396394643217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 129378755866263447438097157 24258516724924396394643217)
                ·
                  refine ⟨18193887543693297295982413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24258516724924396394643217 18193887543693297295982413)
                  ·
                    refine ⟨6822707828884986485993405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18193887543693297295982413 6822707828884986485993405)
                    ·
                      refine ⟨2558515435831869932247527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6822707828884986485993405 2558515435831869932247527)
                      ·
                        rfl

theorem cell23_4982691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2, 3, 3].length) (baseStart_4982691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4982691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4982691 prefixEnd_4982691 := by exact prefixLift 4982691
  have htrace : WordTrace (prefixWord ++ tailWord_4982691) baseStart_4982691 baseEnd_4982691 := by
    simpa [prefixWord, tailWord_4982691, baseEnd_4982691] using wordTrace_append hprefix tailTrace_4982691
  have hstable : (prefixWord ++ tailWord_4982691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4982691).length < 2 ^ (prefixWord ++ tailWord_4982691).sum := by decide
  have hdescent : baseEnd_4982691 < baseStart_4982691 := by decide
  rcases family_descends (prefixWord ++ tailWord_4982691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4982692 : List Nat := [2, 3, 1, 2, 1, 4, 2, 2, 2, 2, 2]
def baseStart_4982692 : Nat := 118140960795 + 4982692 * 2 ^ 59
def prefixEnd_4982692 : Nat := 4983230072969 + 3 ^ 40 * 4982692 * 2
def baseEnd_4982692 : Nat := 2558515949312524428335023

theorem tailTrace_4982692 : CollatzResearch.WordTrace tailWord_4982692 prefixEnd_4982692 2558515949312524428335023 := by
  unfold tailWord_4982692
  simp only [CollatzResearch.WordTrace]
  refine ⟨90866853632282667444523165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121155804843043556592697553 90866853632282667444523165)
  ·
    refine ⟨34075070112106000291696187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90866853632282667444523165 34075070112106000291696187)
    ·
      refine ⟨51112605168159000437544281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34075070112106000291696187 51112605168159000437544281)
      ·
        refine ⟨38334453876119250328158211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51112605168159000437544281 38334453876119250328158211)
        ·
          refine ⟨57501680814178875492237317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38334453876119250328158211 57501680814178875492237317)
          ·
            refine ⟨10781565152658539154794497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57501680814178875492237317 10781565152658539154794497)
            ·
              refine ⟨8086173864493904366095873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10781565152658539154794497 8086173864493904366095873)
              ·
                refine ⟨6064630398370428274571905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8086173864493904366095873 6064630398370428274571905)
                ·
                  refine ⟨4548472798777821205928929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6064630398370428274571905 4548472798777821205928929)
                  ·
                    refine ⟨3411354599083365904446697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4548472798777821205928929 3411354599083365904446697)
                    ·
                      refine ⟨2558515949312524428335023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3411354599083365904446697 2558515949312524428335023)
                      ·
                        rfl

theorem cell23_4982692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 2, 2, 2, 2].length) (baseStart_4982692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4982692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4982692 prefixEnd_4982692 := by exact prefixLift 4982692
  have htrace : WordTrace (prefixWord ++ tailWord_4982692) baseStart_4982692 baseEnd_4982692 := by
    simpa [prefixWord, tailWord_4982692, baseEnd_4982692] using wordTrace_append hprefix tailTrace_4982692
  have hstable : (prefixWord ++ tailWord_4982692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4982692).length < 2 ^ (prefixWord ++ tailWord_4982692).sum := by decide
  have hdescent : baseEnd_4982692 < baseStart_4982692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4982692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4982702 : List Nat := [4, 1, 5, 1, 1, 1, 1, 1, 2, 6]
def baseStart_4982702 : Nat := 118140960795 + 4982702 * 2 ^ 59
def prefixEnd_4982702 : Nat := 4983230072969 + 3 ^ 40 * 4982702 * 2
def baseEnd_4982702 : Nat := 852840361373023129736659

theorem tailTrace_4982702 : CollatzResearch.WordTrace tailWord_4982702 prefixEnd_4982702 852840361373023129736659 := by
  unfold tailWord_4982702
  simp only [CollatzResearch.WordTrace]
  refine ⟨22716758999316138324613795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121156047996352737731273573 22716758999316138324613795)
  ·
    refine ⟨34075138498974207486920693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22716758999316138324613795 34075138498974207486920693)
    ·
      refine ⟨3194544234278831951898815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34075138498974207486920693 3194544234278831951898815)
      ·
        refine ⟨4791816351418247927848223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3194544234278831951898815 4791816351418247927848223)
        ·
          refine ⟨7187724527127371891772335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4791816351418247927848223 7187724527127371891772335)
          ·
            refine ⟨10781586790691057837658503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7187724527127371891772335 10781586790691057837658503)
            ·
              refine ⟨16172380186036586756487755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10781586790691057837658503 16172380186036586756487755)
              ·
                refine ⟨24258570279054880134731633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16172380186036586756487755 24258570279054880134731633)
                ·
                  refine ⟨18193927709291160101048725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24258570279054880134731633 18193927709291160101048725)
                  ·
                    refine ⟨852840361373023129736659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18193927709291160101048725 852840361373023129736659)
                    ·
                      rfl

theorem cell23_4982702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_4982702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4982702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4982702 prefixEnd_4982702 := by exact prefixLift 4982702
  have htrace : WordTrace (prefixWord ++ tailWord_4982702) baseStart_4982702 baseEnd_4982702 := by
    simpa [prefixWord, tailWord_4982702, baseEnd_4982702] using wordTrace_append hprefix tailTrace_4982702
  have hstable : (prefixWord ++ tailWord_4982702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4982702).length < 2 ^ (prefixWord ++ tailWord_4982702).sum := by decide
  have hdescent : baseEnd_4982702 < baseStart_4982702 := by decide
  rcases family_descends (prefixWord ++ tailWord_4982702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4982728 : List Nat := [2, 1, 3, 1, 4, 1, 3, 1, 2, 5]
def baseStart_4982728 : Nat := 118140960795 + 4982728 * 2 ^ 59
def prefixEnd_4982728 : Nat := 4983230072969 + 3 ^ 40 * 4982728 * 2
def baseEnd_4982728 : Nat := 852844811538695429161619

theorem tailTrace_4982728 : CollatzResearch.WordTrace tailWord_4982728 prefixEnd_4982728 852844811538695429161619 := by
  unfold tailWord_4982728
  simp only [CollatzResearch.WordTrace]
  refine ⟨90867510146217456518678419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121156680194956608691571225 90867510146217456518678419)
  ·
    refine ⟨136301265219326184778017629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90867510146217456518678419 136301265219326184778017629)
    ·
      refine ⟨51112974457247319291756611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136301265219326184778017629 51112974457247319291756611)
      ·
        refine ⟨76669461685870978937634917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51112974457247319291756611 76669461685870978937634917)
        ·
          refine ⟨14375524066100808550806547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76669461685870978937634917 14375524066100808550806547)
          ·
            refine ⟨21563286099151212826209821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14375524066100808550806547 21563286099151212826209821)
            ·
              refine ⟨8086232287181704809828683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21563286099151212826209821 8086232287181704809828683)
              ·
                refine ⟨12129348430772557214743025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8086232287181704809828683 12129348430772557214743025)
                ·
                  refine ⟨9097011323079417911057269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12129348430772557214743025 9097011323079417911057269)
                  ·
                    refine ⟨852844811538695429161619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9097011323079417911057269 852844811538695429161619)
                    ·
                      rfl

theorem cell23_4982728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 1, 2, 5].length) (baseStart_4982728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4982728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4982728 prefixEnd_4982728 := by exact prefixLift 4982728
  have htrace : WordTrace (prefixWord ++ tailWord_4982728) baseStart_4982728 baseEnd_4982728 := by
    simpa [prefixWord, tailWord_4982728, baseEnd_4982728] using wordTrace_append hprefix tailTrace_4982728
  have hstable : (prefixWord ++ tailWord_4982728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4982728).length < 2 ^ (prefixWord ++ tailWord_4982728).sum := by decide
  have hdescent : baseEnd_4982728 < baseStart_4982728 := by decide
  rcases family_descends (prefixWord ++ tailWord_4982728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4982731 : List Nat := [1, 1, 1, 1, 3, 4, 3, 1, 1, 3, 4]
def baseStart_4982731 : Nat := 118140960795 + 4982731 * 2 ^ 59
def prefixEnd_4982731 : Nat := 4983230072969 + 3 ^ 40 * 4982731 * 2
def baseEnd_4982731 : Nat := 2558535975058049775747343

theorem tailTrace_4982731 : CollatzResearch.WordTrace tailWord_4982731 prefixEnd_4982731 2558535975058049775747343 := by
  unfold tailWord_4982731
  simp only [CollatzResearch.WordTrace]
  refine ⟨181735129711424044549716047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121156753140949363033144031 181735129711424044549716047)
  ·
    refine ⟨272602694567136066824574071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181735129711424044549716047 272602694567136066824574071)
    ·
      refine ⟨408904041850704100236861107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272602694567136066824574071 408904041850704100236861107)
      ·
        refine ⟨613356062776056150355291661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 408904041850704100236861107 613356062776056150355291661)
        ·
          refine ⟨230008523541021056383234373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 613356062776056150355291661 230008523541021056383234373)
          ·
            refine ⟨43126598163941448071856445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 230008523541021056383234373 43126598163941448071856445)
            ·
              refine ⟨16172474311478043026946167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43126598163941448071856445 16172474311478043026946167)
              ·
                refine ⟨24258711467217064540419251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16172474311478043026946167 24258711467217064540419251)
                ·
                  refine ⟨36388067200825596810628877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24258711467217064540419251 36388067200825596810628877)
                  ·
                    refine ⟨13645525200309598803985829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36388067200825596810628877 13645525200309598803985829)
                    ·
                      refine ⟨2558535975058049775747343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13645525200309598803985829 2558535975058049775747343)
                      ·
                        rfl

theorem cell23_4982731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 3, 4].length) (baseStart_4982731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4982731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4982731 prefixEnd_4982731 := by exact prefixLift 4982731
  have htrace : WordTrace (prefixWord ++ tailWord_4982731) baseStart_4982731 baseEnd_4982731 := by
    simpa [prefixWord, tailWord_4982731, baseEnd_4982731] using wordTrace_append hprefix tailTrace_4982731
  have hstable : (prefixWord ++ tailWord_4982731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4982731).length < 2 ^ (prefixWord ++ tailWord_4982731).sum := by decide
  have hdescent : baseEnd_4982731 < baseStart_4982731 := by decide
  rcases family_descends (prefixWord ++ tailWord_4982731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4982771 : List Nat := [1, 1, 1, 2, 2, 2, 1, 7, 6]
def baseStart_4982771 : Nat := 118140960795 + 4982771 * 2 ^ 59
def prefixEnd_4982771 : Nat := 4983230072969 + 3 ^ 40 * 4982771 * 2
def baseEnd_4982771 : Nat := 284284057142692179916351

theorem tailTrace_4982771 : CollatzResearch.WordTrace tailWord_4982771 prefixEnd_4982771 284284057142692179916351 := by
  unfold tailWord_4982771
  simp only [CollatzResearch.WordTrace]
  refine ⟨181736588631279131381172167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121157725754186087587448111 181736588631279131381172167)
  ·
    refine ⟨272604882946918697071758251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181736588631279131381172167 272604882946918697071758251)
    ·
      refine ⟨408907324420378045607637377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272604882946918697071758251 408907324420378045607637377)
      ·
        refine ⟨306680493315283534205728033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 408907324420378045607637377 306680493315283534205728033)
        ·
          refine ⟨230010369986462650654296025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 306680493315283534205728033 230010369986462650654296025)
          ·
            refine ⟨172507777489846987990722019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 230010369986462650654296025 172507777489846987990722019)
            ·
              refine ⟨258761666234770481986083029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172507777489846987990722019 258761666234770481986083029)
              ·
                refine ⟨6064726552377433171548821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 258761666234770481986083029 6064726552377433171548821)
                ·
                  refine ⟨284284057142692179916351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6064726552377433171548821 284284057142692179916351)
                  ·
                    rfl

theorem cell23_4982771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 7, 6].length) (baseStart_4982771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4982771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4982771 prefixEnd_4982771 := by exact prefixLift 4982771
  have htrace : WordTrace (prefixWord ++ tailWord_4982771) baseStart_4982771 baseEnd_4982771 := by
    simpa [prefixWord, tailWord_4982771, baseEnd_4982771] using wordTrace_append hprefix tailTrace_4982771
  have hstable : (prefixWord ++ tailWord_4982771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4982771).length < 2 ^ (prefixWord ++ tailWord_4982771).sum := by decide
  have hdescent : baseEnd_4982771 < baseStart_4982771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4982771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4982801 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 7, 5]
def baseStart_4982801 : Nat := 118140960795 + 4982801 * 2 ^ 59
def prefixEnd_4982801 : Nat := 4983230072969 + 3 ^ 40 * 4982801 * 2
def baseEnd_4982801 : Nat := 852857306234621500624007

theorem tailTrace_4982801 : CollatzResearch.WordTrace tailWord_4982801 prefixEnd_4982801 852857306234621500624007 := by
  unfold tailWord_4982801
  simp only [CollatzResearch.WordTrace]
  refine ⟨181737682821170446504764257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121158455214113631003176171 181737682821170446504764257)
  ·
    refine ⟨136303262115877834878573193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181737682821170446504764257 136303262115877834878573193)
    ·
      refine ⟨102227446586908376158929895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136303262115877834878573193 102227446586908376158929895)
      ·
        refine ⟨153341169880362564238394843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102227446586908376158929895 153341169880362564238394843)
        ·
          refine ⟨230011754820543846357592265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153341169880362564238394843 230011754820543846357592265)
          ·
            refine ⟨172508816115407884768194199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 230011754820543846357592265 172508816115407884768194199)
            ·
              refine ⟨258763224173111827152291299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172508816115407884768194199 258763224173111827152291299)
              ·
                refine ⟨388144836259667740728436949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 258763224173111827152291299 388144836259667740728436949)
                ·
                  refine ⟨9097144599835962673322741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 388144836259667740728436949 9097144599835962673322741)
                  ·
                    refine ⟨852857306234621500624007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9097144599835962673322741 852857306234621500624007)
                    ·
                      rfl

theorem cell23_4982801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 5].length) (baseStart_4982801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4982801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4982801 prefixEnd_4982801 := by exact prefixLift 4982801
  have htrace : WordTrace (prefixWord ++ tailWord_4982801) baseStart_4982801 baseEnd_4982801 := by
    simpa [prefixWord, tailWord_4982801, baseEnd_4982801] using wordTrace_append hprefix tailTrace_4982801
  have hstable : (prefixWord ++ tailWord_4982801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4982801).length < 2 ^ (prefixWord ++ tailWord_4982801).sum := by decide
  have hdescent : baseEnd_4982801 < baseStart_4982801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4982801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4982818 : List Nat := [3, 3, 1, 1, 1, 2, 2, 2, 3, 5]
def baseStart_4982818 : Nat := 118140960795 + 4982818 * 2 ^ 59
def prefixEnd_4982818 : Nat := 4983230072969 + 3 ^ 40 * 4982818 * 2
def baseEnd_4982818 : Nat := 852860215958330311786481

theorem tailTrace_4982818 : CollatzResearch.WordTrace tailWord_4982818 prefixEnd_4982818 852860215958330311786481 := by
  unfold tailWord_4982818
  simp only [CollatzResearch.WordTrace]
  refine ⟨45434575715527214602033277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121158868574739238938755405 45434575715527214602033277)
  ·
    refine ⟨17037965893322705475762479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45434575715527214602033277 17037965893322705475762479)
    ·
      refine ⟨25556948839984058213643719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17037965893322705475762479 25556948839984058213643719)
      ·
        refine ⟨38335423259976087320465579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25556948839984058213643719 38335423259976087320465579)
        ·
          refine ⟨57503134889964130980698369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38335423259976087320465579 57503134889964130980698369)
          ·
            refine ⟨43127351167473098235523777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57503134889964130980698369 43127351167473098235523777)
            ·
              refine ⟨32345513375604823676642833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43127351167473098235523777 32345513375604823676642833)
              ·
                refine ⟨24259135031703617757482125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32345513375604823676642833 24259135031703617757482125)
                ·
                  refine ⟨9097175636888856659055797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24259135031703617757482125 9097175636888856659055797)
                  ·
                    refine ⟨852860215958330311786481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9097175636888856659055797 852860215958330311786481)
                    ·
                      rfl

theorem cell23_4982818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_4982818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4982818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4982818 prefixEnd_4982818 := by exact prefixLift 4982818
  have htrace : WordTrace (prefixWord ++ tailWord_4982818) baseStart_4982818 baseEnd_4982818 := by
    simpa [prefixWord, tailWord_4982818, baseEnd_4982818] using wordTrace_append hprefix tailTrace_4982818
  have hstable : (prefixWord ++ tailWord_4982818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4982818).length < 2 ^ (prefixWord ++ tailWord_4982818).sum := by decide
  have hdescent : baseEnd_4982818 < baseStart_4982818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4982818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4982848 : List Nat := [2, 1, 1, 2, 2, 5, 1, 2, 1, 6]
def baseStart_4982848 : Nat := 118140960795 + 4982848 * 2 ^ 59
def prefixEnd_4982848 : Nat := 4983230072969 + 3 ^ 40 * 4982848 * 2
def baseEnd_4982848 : Nat := 852865350764875272661435

theorem tailTrace_4982848 : CollatzResearch.WordTrace tailWord_4982848 prefixEnd_4982848 852865350764875272661435 := by
  unfold tailWord_4982848
  simp only [CollatzResearch.WordTrace]
  refine ⟨90869698526000086765862599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121159598034666782354483465 90869698526000086765862599)
  ·
    refine ⟨136304547789000130148793899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90869698526000086765862599 136304547789000130148793899)
    ·
      refine ⟨204456821683500195223190849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136304547789000130148793899 204456821683500195223190849)
      ·
        refine ⟨153342616262625146417393137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204456821683500195223190849 153342616262625146417393137)
        ·
          refine ⟨115006962196968859813044853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153342616262625146417393137 115006962196968859813044853)
          ·
            refine ⟨10781902705965830607472955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 115006962196968859813044853 10781902705965830607472955)
            ·
              refine ⟨16172854058948745911209433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10781902705965830607472955 16172854058948745911209433)
              ·
                refine ⟨12129640544211559433407075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16172854058948745911209433 12129640544211559433407075)
                ·
                  refine ⟨18194460816317339150110613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12129640544211559433407075 18194460816317339150110613)
                  ·
                    refine ⟨852865350764875272661435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18194460816317339150110613 852865350764875272661435)
                    ·
                      rfl

theorem cell23_4982848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 2, 1, 6].length) (baseStart_4982848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4982848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4982848 prefixEnd_4982848 := by exact prefixLift 4982848
  have htrace : WordTrace (prefixWord ++ tailWord_4982848) baseStart_4982848 baseEnd_4982848 := by
    simpa [prefixWord, tailWord_4982848, baseEnd_4982848] using wordTrace_append hprefix tailTrace_4982848
  have hstable : (prefixWord ++ tailWord_4982848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4982848).length < 2 ^ (prefixWord ++ tailWord_4982848).sum := by decide
  have hdescent : baseEnd_4982848 < baseStart_4982848 := by decide
  rcases family_descends (prefixWord ++ tailWord_4982848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4982851 : List Nat := [1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 6]
def baseStart_4982851 : Nat := 118140960795 + 4982851 * 2 ^ 59
def prefixEnd_4982851 : Nat := 4983230072969 + 3 ^ 40 * 4982851 * 2
def baseEnd_4982851 : Nat := 2558597592736589306246791

theorem tailTrace_4982851 : CollatzResearch.WordTrace tailWord_4982851 prefixEnd_4982851 2558597592736589306246791 := by
  unfold tailWord_4982851
  simp only [CollatzResearch.WordTrace]
  refine ⟨181739506470989305044084407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121159670980659536696056271 181739506470989305044084407)
  ·
    refine ⟨272609259706483957566126611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181739506470989305044084407 272609259706483957566126611)
    ·
      refine ⟨408913889559725936349189917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272609259706483957566126611 408913889559725936349189917)
      ·
        refine ⟨153342708584897226130946219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 408913889559725936349189917 153342708584897226130946219)
        ·
          refine ⟨230014062877345839196419329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153342708584897226130946219 230014062877345839196419329)
          ·
            refine ⟨172510547158009379397314497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 230014062877345839196419329 172510547158009379397314497)
            ·
              refine ⟨129382910368507034547985873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 172510547158009379397314497 129382910368507034547985873)
              ·
                refine ⟨97037182776380275910989405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129382910368507034547985873 97037182776380275910989405)
                ·
                  refine ⟨36388943541142603466621027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97037182776380275910989405 36388943541142603466621027)
                  ·
                    refine ⟨54583415311713905199931541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36388943541142603466621027 54583415311713905199931541)
                    ·
                      refine ⟨2558597592736589306246791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54583415311713905199931541 2558597592736589306246791)
                      ·
                        rfl

theorem cell23_4982851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 6].length) (baseStart_4982851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4982851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4982851 prefixEnd_4982851 := by exact prefixLift 4982851
  have htrace : WordTrace (prefixWord ++ tailWord_4982851) baseStart_4982851 baseEnd_4982851 := by
    simpa [prefixWord, tailWord_4982851, baseEnd_4982851] using wordTrace_append hprefix tailTrace_4982851
  have hstable : (prefixWord ++ tailWord_4982851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4982851).length < 2 ^ (prefixWord ++ tailWord_4982851).sum := by decide
  have hdescent : baseEnd_4982851 < baseStart_4982851 := by decide
  rcases family_descends (prefixWord ++ tailWord_4982851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4982868 : List Nat := [2, 4, 1, 1, 1, 1, 1, 1, 5, 2, 4]
def baseStart_4982868 : Nat := 118140960795 + 4982868 * 2 ^ 59
def prefixEnd_4982868 : Nat := 4983230072969 + 3 ^ 40 * 4982868 * 2
def baseEnd_4982868 : Nat := 2558606321907715739734213

theorem tailTrace_4982868 : CollatzResearch.WordTrace tailWord_4982868 prefixEnd_4982868 2558606321907715739734213 := by
  unfold tailWord_4982868
  simp only [CollatzResearch.WordTrace]
  refine ⟨90870063255963858473726629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121160084341285144631635505 90870063255963858473726629)
  ·
    refine ⟨17038136860493223463823743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90870063255963858473726629 17038136860493223463823743)
    ·
      refine ⟨25557205290739835195735615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17038136860493223463823743 25557205290739835195735615)
      ·
        refine ⟨38335807936109752793603423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25557205290739835195735615 38335807936109752793603423)
        ·
          refine ⟨57503711904164629190405135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38335807936109752793603423 57503711904164629190405135)
          ·
            refine ⟨86255567856246943785607703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57503711904164629190405135 86255567856246943785607703)
            ·
              refine ⟨129383351784370415678411555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86255567856246943785607703 129383351784370415678411555)
              ·
                refine ⟨194075027676555623517617333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129383351784370415678411555 194075027676555623517617333)
                ·
                  refine ⟨18194533844677089704776625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 194075027676555623517617333 18194533844677089704776625)
                  ·
                    refine ⟨13645900383507817278582469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18194533844677089704776625 13645900383507817278582469)
                    ·
                      refine ⟨2558606321907715739734213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13645900383507817278582469 2558606321907715739734213)
                      ·
                        rfl

theorem cell23_4982868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_4982868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4982868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4982868 prefixEnd_4982868 := by exact prefixLift 4982868
  have htrace : WordTrace (prefixWord ++ tailWord_4982868) baseStart_4982868 baseEnd_4982868 := by
    simpa [prefixWord, tailWord_4982868, baseEnd_4982868] using wordTrace_append hprefix tailTrace_4982868
  have hstable : (prefixWord ++ tailWord_4982868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4982868).length < 2 ^ (prefixWord ++ tailWord_4982868).sum := by decide
  have hdescent : baseEnd_4982868 < baseStart_4982868 := by decide
  rcases family_descends (prefixWord ++ tailWord_4982868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4982882 : List Nat := [3, 3, 2, 2, 2, 1, 2, 1, 1, 6]
def baseStart_4982882 : Nat := 118140960795 + 4982882 * 2 ^ 59
def prefixEnd_4982882 : Nat := 4983230072969 + 3 ^ 40 * 4982882 * 2
def baseEnd_4982882 : Nat := 852871170212292894986383

theorem tailTrace_4982882 : CollatzResearch.WordTrace tailWord_4982882 prefixEnd_4982882 852871170212292894986383 := by
  unfold tailWord_4982882
  simp only [CollatzResearch.WordTrace]
  refine ⟨45435159283469249334615725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121160424755917998225641933 45435159283469249334615725)
  ·
    refine ⟨17038184731300968500480897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45435159283469249334615725 17038184731300968500480897)
    ·
      refine ⟨12778638548475726375360673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17038184731300968500480897 12778638548475726375360673)
      ·
        refine ⟨9583978911356794781520505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12778638548475726375360673 9583978911356794781520505)
        ·
          refine ⟨7187984183517596086140379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9583978911356794781520505 7187984183517596086140379)
          ·
            refine ⟨10781976275276394129210569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7187984183517596086140379 10781976275276394129210569)
            ·
              refine ⟨8086482206457295596907927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10781976275276394129210569 8086482206457295596907927)
              ·
                refine ⟨12129723309685943395361891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8086482206457295596907927 12129723309685943395361891)
                ·
                  refine ⟨18194584964528915093042837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12129723309685943395361891 18194584964528915093042837)
                  ·
                    refine ⟨852871170212292894986383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18194584964528915093042837 852871170212292894986383)
                    ·
                      rfl

theorem cell23_4982882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_4982882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4982882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4982882 prefixEnd_4982882 := by exact prefixLift 4982882
  have htrace : WordTrace (prefixWord ++ tailWord_4982882) baseStart_4982882 baseEnd_4982882 := by
    simpa [prefixWord, tailWord_4982882, baseEnd_4982882] using wordTrace_append hprefix tailTrace_4982882
  have hstable : (prefixWord ++ tailWord_4982882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4982882).length < 2 ^ (prefixWord ++ tailWord_4982882).sum := by decide
  have hdescent : baseEnd_4982882 < baseStart_4982882 := by decide
  rcases family_descends (prefixWord ++ tailWord_4982882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
