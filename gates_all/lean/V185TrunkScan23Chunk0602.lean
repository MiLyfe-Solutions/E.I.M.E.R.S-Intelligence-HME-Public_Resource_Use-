import V185TrunkScan23Chunk0601

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3560092 : List Nat := [2, 2, 3, 2, 2, 1, 1, 2, 1, 5, 2]
def baseStart_3560092 : Nat := 118140960795 + 3560092 * 2 ^ 59
def prefixEnd_3560092 : Nat := 4983230072969 + 3 ^ 40 * 3560092 * 2
def baseEnd_3560092 : Nat := 1828038370226390357377441

theorem tailTrace_3560092 : CollatzResearch.WordTrace tailWord_3560092 prefixEnd_3560092 1828038370226390357377441 := by
  unfold tailWord_3560092
  simp only [CollatzResearch.WordTrace]
  refine ⟨64923611309201087076069265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86564815078934782768092353 64923611309201087076069265)
  ·
    refine ⟨48692708481900815307051949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64923611309201087076069265 48692708481900815307051949)
    ·
      refine ⟨18259765680712805740144481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48692708481900815307051949 18259765680712805740144481)
      ·
        refine ⟨13694824260534604305108361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18259765680712805740144481 13694824260534604305108361)
        ·
          refine ⟨10271118195400953228831271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13694824260534604305108361 10271118195400953228831271)
          ·
            refine ⟨15406677293101429843246907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10271118195400953228831271 15406677293101429843246907)
            ·
              refine ⟨23110015939652144764870361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15406677293101429843246907 23110015939652144764870361)
              ·
                refine ⟨17332511954739108573652771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23110015939652144764870361 17332511954739108573652771)
                ·
                  refine ⟨25998767932108662860479157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17332511954739108573652771 25998767932108662860479157)
                  ·
                    refine ⟨2437384493635187143169921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25998767932108662860479157 2437384493635187143169921)
                    ·
                      refine ⟨1828038370226390357377441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2437384493635187143169921 1828038370226390357377441)
                      ·
                        rfl

theorem cell23_3560092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_3560092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3560092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3560092 prefixEnd_3560092 := by exact prefixLift 3560092
  have htrace : WordTrace (prefixWord ++ tailWord_3560092) baseStart_3560092 baseEnd_3560092 := by
    simpa [prefixWord, tailWord_3560092, baseEnd_3560092] using wordTrace_append hprefix tailTrace_3560092
  have hstable : (prefixWord ++ tailWord_3560092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560092).length < 2 ^ (prefixWord ++ tailWord_3560092).sum := by decide
  have hdescent : baseEnd_3560092 < baseStart_3560092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560105 : List Nat := [1, 2, 1, 1, 1, 1, 2, 8, 1, 1, 4]
def baseStart_3560105 : Nat := 118140960795 + 3560105 * 2 ^ 59
def prefixEnd_3560105 : Nat := 4983230072969 + 3 ^ 40 * 3560105 * 2
def baseEnd_3560105 : Nat := 1828045045474898806514881

theorem tailTrace_3560105 : CollatzResearch.WordTrace tailWord_3560105 prefixEnd_3560105 1828045045474898806514881 := by
  unfold tailWord_3560105
  simp only [CollatzResearch.WordTrace]
  refine ⟨129847696767355077372361769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86565131178236718248241179 129847696767355077372361769)
  ·
    refine ⟨97385772575516308029271327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129847696767355077372361769 97385772575516308029271327)
    ·
      refine ⟨146078658863274462043906991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97385772575516308029271327 146078658863274462043906991)
      ·
        refine ⟨219117988294911693065860487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146078658863274462043906991 219117988294911693065860487)
        ·
          refine ⟨328676982442367539598790731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219117988294911693065860487 328676982442367539598790731)
          ·
            refine ⟨493015473663551309398186097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328676982442367539598790731 493015473663551309398186097)
            ·
              refine ⟨369761605247663482048639573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 493015473663551309398186097 369761605247663482048639573)
              ·
                refine ⟨4333143811496056430257495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 369761605247663482048639573 4333143811496056430257495)
                ·
                  refine ⟨6499715717244084645386243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4333143811496056430257495 6499715717244084645386243)
                  ·
                    refine ⟨9749573575866126968079365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6499715717244084645386243 9749573575866126968079365)
                    ·
                      refine ⟨1828045045474898806514881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9749573575866126968079365 1828045045474898806514881)
                      ·
                        rfl

theorem cell23_3560105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 8, 1, 1, 4].length) (baseStart_3560105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3560105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3560105 prefixEnd_3560105 := by exact prefixLift 3560105
  have htrace : WordTrace (prefixWord ++ tailWord_3560105) baseStart_3560105 baseEnd_3560105 := by
    simpa [prefixWord, tailWord_3560105, baseEnd_3560105] using wordTrace_append hprefix tailTrace_3560105
  have hstable : (prefixWord ++ tailWord_3560105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560105).length < 2 ^ (prefixWord ++ tailWord_3560105).sum := by decide
  have hdescent : baseEnd_3560105 < baseStart_3560105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560115 : List Nat := [1, 1, 1, 2, 3, 4, 1, 2, 4, 4]
def baseStart_3560115 : Nat := 118140960795 + 3560115 * 2 ^ 59
def prefixEnd_3560115 : Nat := 4983230072969 + 3 ^ 40 * 3560115 * 2
def baseEnd_3560115 : Nat := 609350060093814589129945

theorem tailTrace_3560115 : CollatzResearch.WordTrace tailWord_3560115 prefixEnd_3560115 609350060093814589129945 := by
  unfold tailWord_3560115
  simp only [CollatzResearch.WordTrace]
  refine ⟨129848061497318849080225799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86565374331545899386817199 129848061497318849080225799)
  ·
    refine ⟨194772092245978273620338699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129848061497318849080225799 194772092245978273620338699)
    ·
      refine ⟨292158138368967410430508049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194772092245978273620338699 292158138368967410430508049)
      ·
        refine ⟨219118603776725557822881037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292158138368967410430508049 219118603776725557822881037)
        ·
          refine ⟨82169476416272084183580389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 219118603776725557822881037 82169476416272084183580389)
          ·
            refine ⟨15406776828051015784421323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82169476416272084183580389 15406776828051015784421323)
            ·
              refine ⟨23110165242076523676631985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15406776828051015784421323 23110165242076523676631985)
              ·
                refine ⟨17332623931557392757473989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23110165242076523676631985 17332623931557392757473989)
                ·
                  refine ⟨3249866987167011142026373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17332623931557392757473989 3249866987167011142026373)
                  ·
                    refine ⟨609350060093814589129945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3249866987167011142026373 609350060093814589129945)
                    ·
                      rfl

theorem cell23_3560115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 4, 4].length) (baseStart_3560115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3560115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3560115 prefixEnd_3560115 := by exact prefixLift 3560115
  have htrace : WordTrace (prefixWord ++ tailWord_3560115) baseStart_3560115 baseEnd_3560115 := by
    simpa [prefixWord, tailWord_3560115, baseEnd_3560115] using wordTrace_append hprefix tailTrace_3560115
  have hstable : (prefixWord ++ tailWord_3560115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560115).length < 2 ^ (prefixWord ++ tailWord_3560115).sum := by decide
  have hdescent : baseEnd_3560115 < baseStart_3560115 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560125 : List Nat := [1, 4, 1, 2, 1, 3, 1, 3, 1, 1, 5]
def baseStart_3560125 : Nat := 118140960795 + 3560125 * 2 ^ 59
def prefixEnd_3560125 : Nat := 4983230072969 + 3 ^ 40 * 3560125 * 2
def baseEnd_3560125 : Nat := 1828055315087988728264789

theorem tailTrace_3560125 : CollatzResearch.WordTrace tailWord_3560125 prefixEnd_3560125 1828055315087988728264789 := by
  unfold tailWord_3560125
  simp only [CollatzResearch.WordTrace]
  refine ⟨129848426227282620788089829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86565617484855080525393219 129848426227282620788089829)
  ·
    refine ⟨24346579917615491397766843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129848426227282620788089829 24346579917615491397766843)
    ·
      refine ⟨36519869876423237096650265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24346579917615491397766843 36519869876423237096650265)
      ·
        refine ⟨27389902407317427822487699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36519869876423237096650265 27389902407317427822487699)
        ·
          refine ⟨41084853610976141733731549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27389902407317427822487699 41084853610976141733731549)
          ·
            refine ⟨15406820104116053150149331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41084853610976141733731549 15406820104116053150149331)
            ·
              refine ⟨23110230156174079725223997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15406820104116053150149331 23110230156174079725223997)
              ·
                refine ⟨8666336308565279896958999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23110230156174079725223997 8666336308565279896958999)
                ·
                  refine ⟨12999504462847919845438499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8666336308565279896958999 12999504462847919845438499)
                  ·
                    refine ⟨19499256694271879768157749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12999504462847919845438499 19499256694271879768157749)
                    ·
                      refine ⟨1828055315087988728264789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19499256694271879768157749 1828055315087988728264789)
                      ·
                        rfl

theorem cell23_3560125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_3560125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3560125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3560125 prefixEnd_3560125 := by exact prefixLift 3560125
  have htrace : WordTrace (prefixWord ++ tailWord_3560125) baseStart_3560125 baseEnd_3560125 := by
    simpa [prefixWord, tailWord_3560125, baseEnd_3560125] using wordTrace_append hprefix tailTrace_3560125
  have hstable : (prefixWord ++ tailWord_3560125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560125).length < 2 ^ (prefixWord ++ tailWord_3560125).sum := by decide
  have hdescent : baseEnd_3560125 < baseStart_3560125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560128 : List Nat := [2, 1, 1, 2, 4, 2, 11]
def baseStart_3560128 : Nat := 118140960795 + 3560128 * 2 ^ 59
def prefixEnd_3560128 : Nat := 4983230072969 + 3 ^ 40 * 3560128 * 2
def baseEnd_3560128 : Nat := 22568603154690768105275

theorem tailTrace_3560128 : CollatzResearch.WordTrace tailWord_3560128 prefixEnd_3560128 22568603154690768105275 := by
  unfold tailWord_3560128
  simp only [CollatzResearch.WordTrace]
  refine ⟨64924267823135876150224519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86565690430847834866966025 64924267823135876150224519)
  ·
    refine ⟨97386401734703814225336779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64924267823135876150224519 97386401734703814225336779)
    ·
      refine ⟨146079602602055721338005169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97386401734703814225336779 146079602602055721338005169)
      ·
        refine ⟨109559701951541791003503877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146079602602055721338005169 109559701951541791003503877)
        ·
          refine ⟨20542444115914085813156977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109559701951541791003503877 20542444115914085813156977)
          ·
            refine ⟨15406833086935564359867733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20542444115914085813156977 15406833086935564359867733)
            ·
              refine ⟨22568603154690768105275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 15406833086935564359867733 22568603154690768105275)
              ·
                rfl

theorem cell23_3560128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 11].length) (baseStart_3560128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3560128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3560128 prefixEnd_3560128 := by exact prefixLift 3560128
  have htrace : WordTrace (prefixWord ++ tailWord_3560128) baseStart_3560128 baseEnd_3560128 := by
    simpa [prefixWord, tailWord_3560128, baseEnd_3560128] using wordTrace_append hprefix tailTrace_3560128
  have hstable : (prefixWord ++ tailWord_3560128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560128).length < 2 ^ (prefixWord ++ tailWord_3560128).sum := by decide
  have hdescent : baseEnd_3560128 < baseStart_3560128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560132 : List Nat := [2, 3, 3, 1, 1, 2, 2, 1, 4, 4]
def baseStart_3560132 : Nat := 118140960795 + 3560132 * 2 ^ 59
def prefixEnd_3560132 : Nat := 4983230072969 + 3 ^ 40 * 3560132 * 2
def baseEnd_3560132 : Nat := 609352969817523400292419

theorem tailTrace_3560132 : CollatzResearch.WordTrace tailWord_3560132 prefixEnd_3560132 609352969817523400292419 := by
  unfold tailWord_3560132
  simp only [CollatzResearch.WordTrace]
  refine ⟨64924340769128630491797325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86565787692171507322396433 64924340769128630491797325)
  ·
    refine ⟨24346627788423236434423997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64924340769128630491797325 24346627788423236434423997)
    ·
      refine ⟨9129985420658713662908999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24346627788423236434423997 9129985420658713662908999)
      ·
        refine ⟨13694978130988070494363499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9129985420658713662908999 13694978130988070494363499)
        ·
          refine ⟨20542467196482105741545249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13694978130988070494363499 20542467196482105741545249)
          ·
            refine ⟨15406850397361579306158937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20542467196482105741545249 15406850397361579306158937)
            ·
              refine ⟨11555137798021184479619203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15406850397361579306158937 11555137798021184479619203)
              ·
                refine ⟨17332706697031776719428805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11555137798021184479619203 17332706697031776719428805)
                ·
                  refine ⟨3249882505693458134892901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17332706697031776719428805 3249882505693458134892901)
                  ·
                    refine ⟨609352969817523400292419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3249882505693458134892901 609352969817523400292419)
                    ·
                      rfl

theorem cell23_3560132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_3560132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3560132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3560132 prefixEnd_3560132 := by exact prefixLift 3560132
  have htrace : WordTrace (prefixWord ++ tailWord_3560132) baseStart_3560132 baseEnd_3560132 := by
    simpa [prefixWord, tailWord_3560132, baseEnd_3560132] using wordTrace_append hprefix tailTrace_3560132
  have hstable : (prefixWord ++ tailWord_3560132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560132).length < 2 ^ (prefixWord ++ tailWord_3560132).sum := by decide
  have hdescent : baseEnd_3560132 < baseStart_3560132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560156 : List Nat := [2, 2, 5, 1, 1, 3, 1, 2, 1, 1, 4]
def baseStart_3560156 : Nat := 118140960795 + 3560156 * 2 ^ 59
def prefixEnd_3560156 : Nat := 4983230072969 + 3 ^ 40 * 3560156 * 2
def baseEnd_3560156 : Nat := 1828071232988278106977147

theorem tailTrace_3560156 : CollatzResearch.WordTrace tailWord_3560156 prefixEnd_3560156 1828071232988278106977147 := by
  unfold tailWord_3560156
  simp only [CollatzResearch.WordTrace]
  refine ⟨64924778445085156541234161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86566371260113542054978881 64924778445085156541234161)
  ·
    refine ⟨48693583833813867405925621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64924778445085156541234161 48693583833813867405925621)
    ·
      refine ⟨4565023484420050069305527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48693583833813867405925621 4565023484420050069305527)
      ·
        refine ⟨6847535226630075103958291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4565023484420050069305527 6847535226630075103958291)
        ·
          refine ⟨10271302839945112655937437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6847535226630075103958291 10271302839945112655937437)
          ·
            refine ⟨3851738564979417245976539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10271302839945112655937437 3851738564979417245976539)
            ·
              refine ⟨5777607847469125868964809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3851738564979417245976539 5777607847469125868964809)
              ·
                refine ⟨4333205885601844401723607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5777607847469125868964809 4333205885601844401723607)
                ·
                  refine ⟨6499808828402766602585411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4333205885601844401723607 6499808828402766602585411)
                  ·
                    refine ⟨9749713242604149903878117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6499808828402766602585411 9749713242604149903878117)
                    ·
                      refine ⟨1828071232988278106977147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9749713242604149903878117 1828071232988278106977147)
                      ·
                        rfl

theorem cell23_3560156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_3560156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3560156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3560156 prefixEnd_3560156 := by exact prefixLift 3560156
  have htrace : WordTrace (prefixWord ++ tailWord_3560156) baseStart_3560156 baseEnd_3560156 := by
    simpa [prefixWord, tailWord_3560156, baseEnd_3560156] using wordTrace_append hprefix tailTrace_3560156
  have hstable : (prefixWord ++ tailWord_3560156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560156).length < 2 ^ (prefixWord ++ tailWord_3560156).sum := by decide
  have hdescent : baseEnd_3560156 < baseStart_3560156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560159 : List Nat := [1, 1, 2, 3, 2, 5, 1, 2, 1, 2, 3]
def baseStart_3560159 : Nat := 118140960795 + 3560159 * 2 ^ 59
def prefixEnd_3560159 : Nat := 4983230072969 + 3 ^ 40 * 3560159 * 2
def baseEnd_3560159 : Nat := 1828072773430241595239633

theorem tailTrace_3560159 : CollatzResearch.WordTrace tailWord_3560159 prefixEnd_3560159 1828072773430241595239633 := by
  unfold tailWord_3560159
  simp only [CollatzResearch.WordTrace]
  refine ⟨129849666309159444594827531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86566444206106296396551687 129849666309159444594827531)
  ·
    refine ⟨194774499463739166892241297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129849666309159444594827531 194774499463739166892241297)
    ·
      refine ⟨146080874597804375169180973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194774499463739166892241297 146080874597804375169180973)
      ·
        refine ⟨54780327974176640688442865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146080874597804375169180973 54780327974176640688442865)
        ·
          refine ⟨41085245980632480516332149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54780327974176640688442865 41085245980632480516332149)
          ·
            refine ⟨3851741810684295048406139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41085245980632480516332149 3851741810684295048406139)
            ·
              refine ⟨5777612716026442572609209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3851741810684295048406139 5777612716026442572609209)
              ·
                refine ⟨4333209537019831929456907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5777612716026442572609209 4333209537019831929456907)
                ·
                  refine ⟨6499814305529747894185361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4333209537019831929456907 6499814305529747894185361)
                  ·
                    refine ⟨4874860729147310920639021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6499814305529747894185361 4874860729147310920639021)
                    ·
                      refine ⟨1828072773430241595239633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4874860729147310920639021 1828072773430241595239633)
                      ·
                        rfl

theorem cell23_3560159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 2, 1, 2, 3].length) (baseStart_3560159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3560159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3560159 prefixEnd_3560159 := by exact prefixLift 3560159
  have htrace : WordTrace (prefixWord ++ tailWord_3560159) baseStart_3560159 baseEnd_3560159 := by
    simpa [prefixWord, tailWord_3560159, baseEnd_3560159] using wordTrace_append hprefix tailTrace_3560159
  have hstable : (prefixWord ++ tailWord_3560159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560159).length < 2 ^ (prefixWord ++ tailWord_3560159).sum := by decide
  have hdescent : baseEnd_3560159 < baseStart_3560159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560189 : List Nat := [1, 4, 1, 1, 1, 1, 6, 2, 2, 1, 3]
def baseStart_3560189 : Nat := 118140960795 + 3560189 * 2 ^ 59
def prefixEnd_3560189 : Nat := 4983230072969 + 3 ^ 40 * 3560189 * 2
def baseEnd_3560189 : Nat := 1828088177849876477864495

theorem tailTrace_3560189 : CollatzResearch.WordTrace tailWord_3560189 prefixEnd_3560189 1828088177849876477864495 := by
  unfold tailWord_3560189
  simp only [CollatzResearch.WordTrace]
  refine ⟨129850760499050759718419621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86567173666033839812279747 129850760499050759718419621)
  ·
    refine ⟨24347017593572017447203679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129850760499050759718419621 24347017593572017447203679)
    ·
      refine ⟨36520526390358026170805519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24347017593572017447203679 36520526390358026170805519)
      ·
        refine ⟨54780789585537039256208279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36520526390358026170805519 54780789585537039256208279)
        ·
          refine ⟨82171184378305558884312419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54780789585537039256208279 82171184378305558884312419)
          ·
            refine ⟨123256776567458338326468629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82171184378305558884312419 123256776567458338326468629)
            ·
              refine ⟨5777661401599609609053217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 123256776567458338326468629 5777661401599609609053217)
              ·
                refine ⟨4333246051199707206789913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5777661401599609609053217 4333246051199707206789913)
                ·
                  refine ⟨3249934538399780405092435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4333246051199707206789913 3249934538399780405092435)
                  ·
                    refine ⟨4874901807599670607638653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3249934538399780405092435 4874901807599670607638653)
                    ·
                      refine ⟨1828088177849876477864495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4874901807599670607638653 1828088177849876477864495)
                      ·
                        rfl

theorem cell23_3560189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 2, 2, 1, 3].length) (baseStart_3560189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3560189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3560189 prefixEnd_3560189 := by exact prefixLift 3560189
  have htrace : WordTrace (prefixWord ++ tailWord_3560189) baseStart_3560189 baseEnd_3560189 := by
    simpa [prefixWord, tailWord_3560189, baseEnd_3560189] using wordTrace_append hprefix tailTrace_3560189
  have hstable : (prefixWord ++ tailWord_3560189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560189).length < 2 ^ (prefixWord ++ tailWord_3560189).sum := by decide
  have hdescent : baseEnd_3560189 < baseStart_3560189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560190 : List Nat := [4, 2, 2, 1, 2, 1, 4, 2, 1, 2, 2]
def baseStart_3560190 : Nat := 118140960795 + 3560190 * 2 ^ 59
def prefixEnd_3560190 : Nat := 4983230072969 + 3 ^ 40 * 3560190 * 2
def baseEnd_3560190 : Nat := 1828088691330530973951991

theorem tailTrace_3560190 : CollatzResearch.WordTrace tailWord_3560190 prefixEnd_3560190 1828088691330530973951991 := by
  unfold tailWord_3560190
  simp only [CollatzResearch.WordTrace]
  refine ⟨16231349621505892111150753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86567197981364757926137349 16231349621505892111150753)
  ·
    refine ⟨12173512216129419083363065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16231349621505892111150753 12173512216129419083363065)
    ·
      refine ⟨9130134162097064312522299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12173512216129419083363065 9130134162097064312522299)
      ·
        refine ⟨13695201243145596468783449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9130134162097064312522299 13695201243145596468783449)
        ·
          refine ⟨10271400932359197351587587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13695201243145596468783449 10271400932359197351587587)
          ·
            refine ⟨15407101398538796027381381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10271400932359197351587587 15407101398538796027381381)
            ·
              refine ⟨2888831512226024255134009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15407101398538796027381381 2888831512226024255134009)
              ·
                refine ⟨2166623634169518191350507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2888831512226024255134009 2166623634169518191350507)
                ·
                  refine ⟨3249935451254277287025761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2166623634169518191350507 3249935451254277287025761)
                  ·
                    refine ⟨2437451588440707965269321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3249935451254277287025761 2437451588440707965269321)
                    ·
                      refine ⟨1828088691330530973951991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2437451588440707965269321 1828088691330530973951991)
                      ·
                        rfl

theorem cell23_3560190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_3560190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3560190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3560190 prefixEnd_3560190 := by exact prefixLift 3560190
  have htrace : WordTrace (prefixWord ++ tailWord_3560190) baseStart_3560190 baseEnd_3560190 := by
    simpa [prefixWord, tailWord_3560190, baseEnd_3560190] using wordTrace_append hprefix tailTrace_3560190
  have hstable : (prefixWord ++ tailWord_3560190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560190).length < 2 ^ (prefixWord ++ tailWord_3560190).sum := by decide
  have hdescent : baseEnd_3560190 < baseStart_3560190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560199 : List Nat := [1, 1, 4, 4, 1, 1, 1, 2, 3, 3, 2]
def baseStart_3560199 : Nat := 118140960795 + 3560199 * 2 ^ 59
def prefixEnd_3560199 : Nat := 4983230072969 + 3 ^ 40 * 3560199 * 2
def baseEnd_3560199 : Nat := 1828093312656421438739449

theorem tailTrace_3560199 : CollatzResearch.WordTrace tailWord_3560199 prefixEnd_3560199 1828093312656421438739449 := by
  unfold tailWord_3560199
  simp only [CollatzResearch.WordTrace]
  refine ⟨129851125229014531426283651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86567416819343020950855767 129851125229014531426283651)
  ·
    refine ⟨194776687843521797139425477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129851125229014531426283651 194776687843521797139425477)
    ·
      refine ⟨36520628970660336963642277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194776687843521797139425477 36520628970660336963642277)
      ·
        refine ⟨6847617931998813180682927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36520628970660336963642277 6847617931998813180682927)
        ·
          refine ⟨10271426897998219771024391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6847617931998813180682927 10271426897998219771024391)
          ·
            refine ⟨15407140346997329656536587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10271426897998219771024391 15407140346997329656536587)
            ·
              refine ⟨23110710520495994484804881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15407140346997329656536587 23110710520495994484804881)
              ·
                refine ⟨17333032890371995863603661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23110710520495994484804881 17333032890371995863603661)
                ·
                  refine ⟨6499887333889498448851373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17333032890371995863603661 6499887333889498448851373)
                  ·
                    refine ⟨2437457750208561918319265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6499887333889498448851373 2437457750208561918319265)
                    ·
                      refine ⟨1828093312656421438739449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2437457750208561918319265 1828093312656421438739449)
                      ·
                        rfl

theorem cell23_3560199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_3560199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3560199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3560199 prefixEnd_3560199 := by exact prefixLift 3560199
  have htrace : WordTrace (prefixWord ++ tailWord_3560199) baseStart_3560199 baseEnd_3560199 := by
    simpa [prefixWord, tailWord_3560199, baseEnd_3560199] using wordTrace_append hprefix tailTrace_3560199
  have hstable : (prefixWord ++ tailWord_3560199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560199).length < 2 ^ (prefixWord ++ tailWord_3560199).sum := by decide
  have hdescent : baseEnd_3560199 < baseStart_3560199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560225 : List Nat := [1, 2, 3, 2, 1, 2, 1, 2, 1, 4, 4]
def baseStart_3560225 : Nat := 118140960795 + 3560225 * 2 ^ 59
def prefixEnd_3560225 : Nat := 4983230072969 + 3 ^ 40 * 3560225 * 2
def baseEnd_3560225 : Nat := 1828106663153438337014329

theorem tailTrace_3560225 : CollatzResearch.WordTrace tailWord_3560225 prefixEnd_3560225 1828106663153438337014329 := by
  unfold tailWord_3560225
  simp only [CollatzResearch.WordTrace]
  refine ⟨129852073526920337866730129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86568049017946891911153419 129852073526920337866730129)
  ·
    refine ⟨97389055145190253400047597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129852073526920337866730129 97389055145190253400047597)
    ·
      refine ⟨36520895679446345025017849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97389055145190253400047597 36520895679446345025017849)
      ·
        refine ⟨27390671759584758768763387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36520895679446345025017849 27390671759584758768763387)
        ·
          refine ⟨41086007639377138153145081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27390671759584758768763387 41086007639377138153145081)
          ·
            refine ⟨30814505729532853614858811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41086007639377138153145081 30814505729532853614858811)
            ·
              refine ⟨46221758594299280422288217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30814505729532853614858811 46221758594299280422288217)
              ·
                refine ⟨34666318945724460316716163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46221758594299280422288217 34666318945724460316716163)
                ·
                  refine ⟨51999478418586690475074245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34666318945724460316716163 51999478418586690475074245)
                  ·
                    refine ⟨9749902203485004464076421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51999478418586690475074245 9749902203485004464076421)
                    ·
                      refine ⟨1828106663153438337014329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9749902203485004464076421 1828106663153438337014329)
                      ·
                        rfl

theorem cell23_3560225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_3560225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3560225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3560225 prefixEnd_3560225 := by exact prefixLift 3560225
  have htrace : WordTrace (prefixWord ++ tailWord_3560225) baseStart_3560225 baseEnd_3560225 := by
    simpa [prefixWord, tailWord_3560225, baseEnd_3560225] using wordTrace_append hprefix tailTrace_3560225
  have hstable : (prefixWord ++ tailWord_3560225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560225).length < 2 ^ (prefixWord ++ tailWord_3560225).sum := by decide
  have hdescent : baseEnd_3560225 < baseStart_3560225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560229 : List Nat := [1, 3, 1, 2, 3, 1, 2, 2, 4, 2, 2]
def baseStart_3560229 : Nat := 118140960795 + 3560229 * 2 ^ 59
def prefixEnd_3560229 : Nat := 4983230072969 + 3 ^ 40 * 3560229 * 2
def baseEnd_3560229 : Nat := 1828108717076056321364311

theorem tailTrace_3560229 : CollatzResearch.WordTrace tailWord_3560229 prefixEnd_3560229 1828108717076056321364311 := by
  unfold tailWord_3560229
  simp only [CollatzResearch.WordTrace]
  refine ⟨129852219418905846549875741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86568146279270564366583827 129852219418905846549875741)
  ·
    refine ⟨48694582282089692456203403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129852219418905846549875741 48694582282089692456203403)
    ·
      refine ⟨73041873423134538684305105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48694582282089692456203403 73041873423134538684305105)
      ·
        refine ⟨54781405067350904013228829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73041873423134538684305105 54781405067350904013228829)
        ·
          refine ⟨20543026900256589004960811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54781405067350904013228829 20543026900256589004960811)
          ·
            refine ⟨30814540350384883507441217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20543026900256589004960811 30814540350384883507441217)
            ·
              refine ⟨23110905262788662630580913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30814540350384883507441217 23110905262788662630580913)
              ·
                refine ⟨17333178947091496972935685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23110905262788662630580913 17333178947091496972935685)
                ·
                  refine ⟨3249971052579655682425441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17333178947091496972935685 3249971052579655682425441)
                  ·
                    refine ⟨2437478289434741761819081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3249971052579655682425441 2437478289434741761819081)
                    ·
                      refine ⟨1828108717076056321364311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2437478289434741761819081 1828108717076056321364311)
                      ·
                        rfl

theorem cell23_3560229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 4, 2, 2].length) (baseStart_3560229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3560229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3560229 prefixEnd_3560229 := by exact prefixLift 3560229
  have htrace : WordTrace (prefixWord ++ tailWord_3560229) baseStart_3560229 baseEnd_3560229 := by
    simpa [prefixWord, tailWord_3560229, baseEnd_3560229] using wordTrace_append hprefix tailTrace_3560229
  have hstable : (prefixWord ++ tailWord_3560229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560229).length < 2 ^ (prefixWord ++ tailWord_3560229).sum := by decide
  have hdescent : baseEnd_3560229 < baseStart_3560229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560265 : List Nat := [1, 2, 1, 1, 2, 5, 1, 2, 1, 7]
def baseStart_3560265 : Nat := 118140960795 + 3560265 * 2 ^ 59
def prefixEnd_3560265 : Nat := 4983230072969 + 3 ^ 40 * 3560265 * 2
def baseEnd_3560265 : Nat := 609375734126539393504715

theorem tailTrace_3560265 : CollatzResearch.WordTrace tailWord_3560265 prefixEnd_3560265 609375734126539393504715 := by
  unfold tailWord_3560265
  simp only [CollatzResearch.WordTrace]
  refine ⟨129853532446775424698186249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86569021631183616465457499 129853532446775424698186249)
  ·
    refine ⟨97390149335081568523639687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129853532446775424698186249 97390149335081568523639687)
    ·
      refine ⟨146085224002622352785459531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97390149335081568523639687 146085224002622352785459531)
      ·
        refine ⟨219127836003933529178189297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146085224002622352785459531 219127836003933529178189297)
        ·
          refine ⟨164345877002950146883641973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219127836003933529178189297 164345877002950146883641973)
          ·
            refine ⟨15407425969026576270341435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 164345877002950146883641973 15407425969026576270341435)
            ·
              refine ⟨23111138953539864405512153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15407425969026576270341435 23111138953539864405512153)
              ·
                refine ⟨17333354215154898304134115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23111138953539864405512153 17333354215154898304134115)
                ·
                  refine ⟨26000031322732347456201173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17333354215154898304134115 26000031322732347456201173)
                  ·
                    refine ⟨609375734126539393504715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26000031322732347456201173 609375734126539393504715)
                    ·
                      rfl

theorem cell23_3560265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 7].length) (baseStart_3560265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3560265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3560265 prefixEnd_3560265 := by exact prefixLift 3560265
  have htrace : WordTrace (prefixWord ++ tailWord_3560265) baseStart_3560265 baseEnd_3560265 := by
    simpa [prefixWord, tailWord_3560265, baseEnd_3560265] using wordTrace_append hprefix tailTrace_3560265
  have hstable : (prefixWord ++ tailWord_3560265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560265).length < 2 ^ (prefixWord ++ tailWord_3560265).sum := by decide
  have hdescent : baseEnd_3560265 < baseStart_3560265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560272 : List Nat := [2, 1, 1, 1, 1, 4, 2, 2, 2, 5, 2]
def baseStart_3560272 : Nat := 118140960795 + 3560272 * 2 ^ 59
def prefixEnd_3560272 : Nat := 4983230072969 + 3 ^ 40 * 3560272 * 2
def baseEnd_3560272 : Nat := 1828130796744199653126613

theorem tailTrace_3560272 : CollatzResearch.WordTrace tailWord_3560272 prefixEnd_3560272 1828130796744199653126613 := by
  unfold tailWord_3560272
  simp only [CollatzResearch.WordTrace]
  refine ⟨64926893878875032446845535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86569191838500043262460713 64926893878875032446845535)
  ·
    refine ⟨97390340818312548670268303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64926893878875032446845535 97390340818312548670268303)
    ·
      refine ⟨146085511227468823005402455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97390340818312548670268303 146085511227468823005402455)
      ·
        refine ⟨219128266841203234508103683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146085511227468823005402455 219128266841203234508103683)
        ·
          refine ⟨328692400261804851762155525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219128266841203234508103683 328692400261804851762155525)
          ·
            refine ⟨61629825049088409705404161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 328692400261804851762155525 61629825049088409705404161)
            ·
              refine ⟨46222368786816307279053121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61629825049088409705404161 46222368786816307279053121)
              ·
                refine ⟨34666776590112230459289841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46222368786816307279053121 34666776590112230459289841)
                ·
                  refine ⟨26000082442584172844467381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34666776590112230459289841 26000082442584172844467381)
                  ·
                    refine ⟨2437507728992266204168817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26000082442584172844467381 2437507728992266204168817)
                    ·
                      refine ⟨1828130796744199653126613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2437507728992266204168817 1828130796744199653126613)
                      ·
                        rfl

theorem cell23_3560272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 2, 5, 2].length) (baseStart_3560272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3560272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3560272 prefixEnd_3560272 := by exact prefixLift 3560272
  have htrace : WordTrace (prefixWord ++ tailWord_3560272) baseStart_3560272 baseEnd_3560272 := by
    simpa [prefixWord, tailWord_3560272, baseEnd_3560272] using wordTrace_append hprefix tailTrace_3560272
  have hstable : (prefixWord ++ tailWord_3560272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560272).length < 2 ^ (prefixWord ++ tailWord_3560272).sum := by decide
  have hdescent : baseEnd_3560272 < baseStart_3560272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560312 : List Nat := [2, 1, 2, 1, 1, 1, 1, 7, 3, 4]
def baseStart_3560312 : Nat := 118140960795 + 3560312 * 2 ^ 59
def prefixEnd_3560312 : Nat := 4983230072969 + 3 ^ 40 * 3560312 * 2
def baseEnd_3560312 : Nat := 609383778656793165542143

theorem tailTrace_3560312 : CollatzResearch.WordTrace tailWord_3560312 prefixEnd_3560312 609383778656793165542143 := by
  unfold tailWord_3560312
  simp only [CollatzResearch.WordTrace]
  refine ⟨64927623338802575862573595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86570164451736767816764793 64927623338802575862573595)
  ·
    refine ⟨97391435008203863793860393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64927623338802575862573595 97391435008203863793860393)
    ·
      refine ⟨73043576256152897845395295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97391435008203863793860393 73043576256152897845395295)
      ·
        refine ⟨109565364384229346768092943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73043576256152897845395295 109565364384229346768092943)
        ·
          refine ⟨164348046576344020152139415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109565364384229346768092943 164348046576344020152139415)
          ·
            refine ⟨246522069864516030228209123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164348046576344020152139415 246522069864516030228209123)
            ·
              refine ⟨369783104796774045342313685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246522069864516030228209123 369783104796774045342313685)
              ·
                refine ⟨8666791518674391687710477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 369783104796774045342313685 8666791518674391687710477)
                ·
                  refine ⟨3250046819502896882891429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8666791518674391687710477 3250046819502896882891429)
                  ·
                    refine ⟨609383778656793165542143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3250046819502896882891429 609383778656793165542143)
                    ·
                      rfl

theorem cell23_3560312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7, 3, 4].length) (baseStart_3560312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3560312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3560312 prefixEnd_3560312 := by exact prefixLift 3560312
  have htrace : WordTrace (prefixWord ++ tailWord_3560312) baseStart_3560312 baseEnd_3560312 := by
    simpa [prefixWord, tailWord_3560312, baseEnd_3560312] using wordTrace_append hprefix tailTrace_3560312
  have hstable : (prefixWord ++ tailWord_3560312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560312).length < 2 ^ (prefixWord ++ tailWord_3560312).sum := by decide
  have hdescent : baseEnd_3560312 < baseStart_3560312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560315 : List Nat := [1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 6]
def baseStart_3560315 : Nat := 118140960795 + 3560315 * 2 ^ 59
def prefixEnd_3560315 : Nat := 4983230072969 + 3 ^ 40 * 3560315 * 2
def baseEnd_3560315 : Nat := 1828152876412342984888915

theorem tailTrace_3560315 : CollatzResearch.WordTrace tailWord_3560315 prefixEnd_3560315 1828152876412342984888915 := by
  unfold tailWord_3560315
  simp only [CollatzResearch.WordTrace]
  refine ⟨129855356096594283237506399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86570237397729522158337599 129855356096594283237506399)
  ·
    refine ⟨194783034144891424856259599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129855356096594283237506399 194783034144891424856259599)
    ·
      refine ⟨292174551217337137284389399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194783034144891424856259599 292174551217337137284389399)
      ·
        refine ⟨438261826826005705926584099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292174551217337137284389399 438261826826005705926584099)
        ·
          refine ⟨657392740239008558889876149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 438261826826005705926584099 657392740239008558889876149)
          ·
            refine ⟨61630569397407052395925889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 657392740239008558889876149 61630569397407052395925889)
            ·
              refine ⟨46222927048055289296944417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61630569397407052395925889 46222927048055289296944417)
              ·
                refine ⟨34667195286041466972708313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46222927048055289296944417 34667195286041466972708313)
                ·
                  refine ⟨26000396464531100229531235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34667195286041466972708313 26000396464531100229531235)
                  ·
                    refine ⟨39000594696796650344296853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26000396464531100229531235 39000594696796650344296853)
                    ·
                      refine ⟨1828152876412342984888915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39000594696796650344296853 1828152876412342984888915)
                      ·
                        rfl

theorem cell23_3560315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 6].length) (baseStart_3560315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3560315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3560315 prefixEnd_3560315 := by exact prefixLift 3560315
  have htrace : WordTrace (prefixWord ++ tailWord_3560315) baseStart_3560315 baseEnd_3560315 := by
    simpa [prefixWord, tailWord_3560315, baseEnd_3560315] using wordTrace_append hprefix tailTrace_3560315
  have hstable : (prefixWord ++ tailWord_3560315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560315).length < 2 ^ (prefixWord ++ tailWord_3560315).sum := by decide
  have hdescent : baseEnd_3560315 < baseStart_3560315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560345 : List Nat := [1, 2, 1, 2, 1, 3, 1, 2, 1, 1, 8]
def baseStart_3560345 : Nat := 118140960795 + 3560345 * 2 ^ 59
def prefixEnd_3560345 : Nat := 4983230072969 + 3 ^ 40 * 3560345 * 2
def baseEnd_3560345 : Nat := 1828168280831977867513777

theorem tailTrace_3560345 : CollatzResearch.WordTrace tailWord_3560345 prefixEnd_3560345 1828168280831977867513777 := by
  unfold tailWord_3560345
  simp only [CollatzResearch.WordTrace]
  refine ⟨129856450286485598361098489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86570966857657065574065659 129856450286485598361098489)
  ·
    refine ⟨97392337714864198770823867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129856450286485598361098489 97392337714864198770823867)
    ·
      refine ⟨146088506572296298156235801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97392337714864198770823867 146088506572296298156235801)
      ·
        refine ⟨109566379929222223617176851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146088506572296298156235801 109566379929222223617176851)
        ·
          refine ⟨164349569893833335425765277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109566379929222223617176851 164349569893833335425765277)
          ·
            refine ⟨61631088710187500784661979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164349569893833335425765277 61631088710187500784661979)
            ·
              refine ⟨92446633065281251176992969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61631088710187500784661979 92446633065281251176992969)
              ·
                refine ⟨69334974798960938382744727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92446633065281251176992969 69334974798960938382744727)
                ·
                  refine ⟨104002462198441407574117091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69334974798960938382744727 104002462198441407574117091)
                  ·
                    refine ⟨156003693297662111361175637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 104002462198441407574117091 156003693297662111361175637)
                    ·
                      refine ⟨1828168280831977867513777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 156003693297662111361175637 1828168280831977867513777)
                      ·
                        rfl

theorem cell23_3560345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 1, 8].length) (baseStart_3560345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3560345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3560345 prefixEnd_3560345 := by exact prefixLift 3560345
  have htrace : WordTrace (prefixWord ++ tailWord_3560345) baseStart_3560345 baseEnd_3560345 := by
    simpa [prefixWord, tailWord_3560345, baseEnd_3560345] using wordTrace_append hprefix tailTrace_3560345
  have hstable : (prefixWord ++ tailWord_3560345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560345).length < 2 ^ (prefixWord ++ tailWord_3560345).sum := by decide
  have hdescent : baseEnd_3560345 < baseStart_3560345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560382 : List Nat := [4, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7]
def baseStart_3560382 : Nat := 118140960795 + 3560382 * 2 ^ 59
def prefixEnd_3560382 : Nat := 4983230072969 + 3 ^ 40 * 3560382 * 2
def baseEnd_3560382 : Nat := 1828187279616194222751107

theorem tailTrace_3560382 : CollatzResearch.WordTrace tailWord_3560382 prefixEnd_3560382 1828187279616194222751107 := by
  unfold tailWord_3560382
  simp only [CollatzResearch.WordTrace]
  refine ⟨16232224973418944210024425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86571866524901035786796933 16232224973418944210024425)
  ·
    refine ⟨12174168730064208157518319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16232224973418944210024425 12174168730064208157518319)
    ·
      refine ⟨18261253095096312236277479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12174168730064208157518319 18261253095096312236277479)
      ·
        refine ⟨27391879642644468354416219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18261253095096312236277479 27391879642644468354416219)
        ·
          refine ⟨41087819463966702531624329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27391879642644468354416219 41087819463966702531624329)
          ·
            refine ⟨30815864597975026898718247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41087819463966702531624329 30815864597975026898718247)
            ·
              refine ⟨46223796896962540348077371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30815864597975026898718247 46223796896962540348077371)
              ·
                refine ⟨69335695345443810522116057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46223796896962540348077371 69335695345443810522116057)
                ·
                  refine ⟨52001771509082857891587043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69335695345443810522116057 52001771509082857891587043)
                  ·
                    refine ⟨78002657263624286837380565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52001771509082857891587043 78002657263624286837380565)
                    ·
                      refine ⟨1828187279616194222751107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 78002657263624286837380565 1828187279616194222751107)
                      ·
                        rfl

theorem cell23_3560382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_3560382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3560382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3560382 prefixEnd_3560382 := by exact prefixLift 3560382
  have htrace : WordTrace (prefixWord ++ tailWord_3560382) baseStart_3560382 baseEnd_3560382 := by
    simpa [prefixWord, tailWord_3560382, baseEnd_3560382] using wordTrace_append hprefix tailTrace_3560382
  have hstable : (prefixWord ++ tailWord_3560382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560382).length < 2 ^ (prefixWord ++ tailWord_3560382).sum := by decide
  have hdescent : baseEnd_3560382 < baseStart_3560382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560419 : List Nat := [1, 1, 1, 6, 1, 1, 3, 1, 4, 4]
def baseStart_3560419 : Nat := 118140960795 + 3560419 * 2 ^ 59
def prefixEnd_3560419 : Nat := 4983230072969 + 3 ^ 40 * 3560419 * 2
def baseEnd_3560419 : Nat := 609402092800136859329479

theorem tailTrace_3560419 : CollatzResearch.WordTrace tailWord_3560419 prefixEnd_3560419 609402092800136859329479 := by
  unfold tailWord_3560419
  simp only [CollatzResearch.WordTrace]
  refine ⟨129859149288217508999292311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86572766192145005999528207 129859149288217508999292311)
  ·
    refine ⟨194788723932326263498938467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129859149288217508999292311 194788723932326263498938467)
    ·
      refine ⟨292183085898489395248407701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194788723932326263498938467 292183085898489395248407701)
      ·
        refine ⟨13696082151491690402269111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 292183085898489395248407701 13696082151491690402269111)
        ·
          refine ⟨20544123227237535603403667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13696082151491690402269111 20544123227237535603403667)
          ·
            refine ⟨30816184840856303405105501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20544123227237535603403667 30816184840856303405105501)
            ·
              refine ⟨11556069315321113776914563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30816184840856303405105501 11556069315321113776914563)
              ·
                refine ⟨17334103972981670665371845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11556069315321113776914563 17334103972981670665371845)
                ·
                  refine ⟨3250144494934063249757221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17334103972981670665371845 3250144494934063249757221)
                  ·
                    refine ⟨609402092800136859329479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3250144494934063249757221 609402092800136859329479)
                    ·
                      rfl

theorem cell23_3560419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 4, 4].length) (baseStart_3560419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3560419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3560419 prefixEnd_3560419 := by exact prefixLift 3560419
  have htrace : WordTrace (prefixWord ++ tailWord_3560419) baseStart_3560419 baseEnd_3560419 := by
    simpa [prefixWord, tailWord_3560419, baseEnd_3560419] using wordTrace_append hprefix tailTrace_3560419
  have hstable : (prefixWord ++ tailWord_3560419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560419).length < 2 ^ (prefixWord ++ tailWord_3560419).sum := by decide
  have hdescent : baseEnd_3560419 < baseStart_3560419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560449 : List Nat := [1, 2, 4, 1, 2, 2, 4, 7]
def baseStart_3560449 : Nat := 118140960795 + 3560449 * 2 ^ 59
def prefixEnd_3560449 : Nat := 4983230072969 + 3 ^ 40 * 3560449 * 2
def baseEnd_3560449 : Nat := 67711914178520202244937

theorem tailTrace_3560449 : CollatzResearch.WordTrace tailWord_3560449 prefixEnd_3560449 67711914178520202244937 := by
  unfold tailWord_3560449
  simp only [CollatzResearch.WordTrace]
  refine ⟨129860243478108824122884401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86573495652072549415256267 129860243478108824122884401)
  ·
    refine ⟨97395182608581618092163301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129860243478108824122884401 97395182608581618092163301)
    ·
      refine ⟨18261596739109053392280619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97395182608581618092163301 18261596739109053392280619)
      ·
        refine ⟨27392395108663580088420929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18261596739109053392280619 27392395108663580088420929)
        ·
          refine ⟨20544296331497685066315697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27392395108663580088420929 20544296331497685066315697)
          ·
            refine ⟨15408222248623263799736773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20544296331497685066315697 15408222248623263799736773)
            ·
              refine ⟨2889041671616861962450645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15408222248623263799736773 2889041671616861962450645)
              ·
                refine ⟨67711914178520202244937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2889041671616861962450645 67711914178520202244937)
                ·
                  rfl

theorem cell23_3560449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 7].length) (baseStart_3560449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3560449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3560449 prefixEnd_3560449 := by exact prefixLift 3560449
  have htrace : WordTrace (prefixWord ++ tailWord_3560449) baseStart_3560449 baseEnd_3560449 := by
    simpa [prefixWord, tailWord_3560449, baseEnd_3560449] using wordTrace_append hprefix tailTrace_3560449
  have hstable : (prefixWord ++ tailWord_3560449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560449).length < 2 ^ (prefixWord ++ tailWord_3560449).sum := by decide
  have hdescent : baseEnd_3560449 < baseStart_3560449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560460 : List Nat := [2, 2, 1, 2, 3, 2, 3, 3, 1, 2, 2]
def baseStart_3560460 : Nat := 118140960795 + 3560460 * 2 ^ 59
def prefixEnd_3560460 : Nat := 4983230072969 + 3 ^ 40 * 3560460 * 2
def baseEnd_3560460 : Nat := 1828227331107244917575749

theorem tailTrace_3560460 : CollatzResearch.WordTrace tailWord_3560460 prefixEnd_3560460 1828227331107244917575749 := by
  unfold tailWord_3560460
  simp only [CollatzResearch.WordTrace]
  refine ⟨64930322340534486500767417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86573763120712648667689889 64930322340534486500767417)
  ·
    refine ⟨48697741755400864875575563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64930322340534486500767417 48697741755400864875575563)
    ·
      refine ⟨73046612633101297313363345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48697741755400864875575563 73046612633101297313363345)
      ·
        refine ⟨54784959474825972985022509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73046612633101297313363345 54784959474825972985022509)
        ·
          refine ⟨20544359803059739869383441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54784959474825972985022509 20544359803059739869383441)
          ·
            refine ⟨15408269852294804902037581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20544359803059739869383441 15408269852294804902037581)
            ·
              refine ⟨5778101194610551838264093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15408269852294804902037581 5778101194610551838264093)
              ·
                refine ⟨2166787947978956939349035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5778101194610551838264093 2166787947978956939349035)
                ·
                  refine ⟨3250181921968435409023553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2166787947978956939349035 3250181921968435409023553)
                  ·
                    refine ⟨2437636441476326556767665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3250181921968435409023553 2437636441476326556767665)
                    ·
                      refine ⟨1828227331107244917575749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2437636441476326556767665 1828227331107244917575749)
                      ·
                        rfl

theorem cell23_3560460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 3, 1, 2, 2].length) (baseStart_3560460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3560460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3560460 prefixEnd_3560460 := by exact prefixLift 3560460
  have htrace : WordTrace (prefixWord ++ tailWord_3560460) baseStart_3560460 baseEnd_3560460 := by
    simpa [prefixWord, tailWord_3560460, baseEnd_3560460] using wordTrace_append hprefix tailTrace_3560460
  have hstable : (prefixWord ++ tailWord_3560460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560460).length < 2 ^ (prefixWord ++ tailWord_3560460).sum := by decide
  have hdescent : baseEnd_3560460 < baseStart_3560460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560477 : List Nat := [1, 4, 2, 2, 4, 1, 1, 1, 3, 2, 2]
def baseStart_3560477 : Nat := 118140960795 + 3560477 * 2 ^ 59
def prefixEnd_3560477 : Nat := 4983230072969 + 3 ^ 40 * 3560477 * 2
def baseEnd_3560477 : Nat := 1828236060278371351063171

theorem tailTrace_3560477 : CollatzResearch.WordTrace tailWord_3560477 prefixEnd_3560477 1828236060278371351063171 := by
  unfold tailWord_3560477
  simp only [CollatzResearch.WordTrace]
  refine ⟨129861264722007384904903685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86574176481338256603269123 129861264722007384904903685)
  ·
    refine ⟨24348987135376384669669441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129861264722007384904903685 24348987135376384669669441)
    ·
      refine ⟨18261740351532288502252081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24348987135376384669669441 18261740351532288502252081)
      ·
        refine ⟨13696305263649216376689061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18261740351532288502252081 13696305263649216376689061)
        ·
          refine ⟨2568057236934228070629199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13696305263649216376689061 2568057236934228070629199)
          ·
            refine ⟨3852085855401342105943799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2568057236934228070629199 3852085855401342105943799)
            ·
              refine ⟨5778128783102013158915699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3852085855401342105943799 5778128783102013158915699)
              ·
                refine ⟨8667193174653019738373549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5778128783102013158915699 8667193174653019738373549)
                ·
                  refine ⟨3250197440494882401890081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8667193174653019738373549 3250197440494882401890081)
                  ·
                    refine ⟨2437648080371161801417561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3250197440494882401890081 2437648080371161801417561)
                    ·
                      refine ⟨1828236060278371351063171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2437648080371161801417561 1828236060278371351063171)
                      ·
                        rfl

theorem cell23_3560477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_3560477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3560477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3560477 prefixEnd_3560477 := by exact prefixLift 3560477
  have htrace : WordTrace (prefixWord ++ tailWord_3560477) baseStart_3560477 baseEnd_3560477 := by
    simpa [prefixWord, tailWord_3560477, baseEnd_3560477] using wordTrace_append hprefix tailTrace_3560477
  have hstable : (prefixWord ++ tailWord_3560477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560477).length < 2 ^ (prefixWord ++ tailWord_3560477).sum := by decide
  have hdescent : baseEnd_3560477 < baseStart_3560477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560492 : List Nat := [2, 2, 1, 1, 1, 2, 4, 1, 1, 8]
def baseStart_3560492 : Nat := 118140960795 + 3560492 * 2 ^ 59
def prefixEnd_3560492 : Nat := 4983230072969 + 3 ^ 40 * 3560492 * 2
def baseEnd_3560492 : Nat := 609414587496062930791867

theorem tailTrace_3560492 : CollatzResearch.WordTrace tailWord_3560492 prefixEnd_3560492 609414587496062930791867 := by
  unfold tailWord_3560492
  simp only [CollatzResearch.WordTrace]
  refine ⟨64930905908476521233349865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86574541211302028311133153 64930905908476521233349865)
  ·
    refine ⟨48698179431357390925012399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64930905908476521233349865 48698179431357390925012399)
    ·
      refine ⟨73047269147036086387518599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48698179431357390925012399 73047269147036086387518599)
      ·
        refine ⟨109570903720554129581277899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73047269147036086387518599 109570903720554129581277899)
        ·
          refine ⟨164356355580831194371916849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109570903720554129581277899 164356355580831194371916849)
          ·
            refine ⟨123267266685623395778937637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164356355580831194371916849 123267266685623395778937637)
            ·
              refine ⟨23112612503554386708550807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123267266685623395778937637 23112612503554386708550807)
              ·
                refine ⟨34668918755331580062826211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23112612503554386708550807 34668918755331580062826211)
                ·
                  refine ⟨52003378132997370094239317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34668918755331580062826211 52003378132997370094239317)
                  ·
                    refine ⟨609414587496062930791867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 52003378132997370094239317 609414587496062930791867)
                    ·
                      rfl

theorem cell23_3560492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 8].length) (baseStart_3560492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3560492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3560492 prefixEnd_3560492 := by exact prefixLift 3560492
  have htrace : WordTrace (prefixWord ++ tailWord_3560492) baseStart_3560492 baseEnd_3560492 := by
    simpa [prefixWord, tailWord_3560492, baseEnd_3560492] using wordTrace_append hprefix tailTrace_3560492
  have hstable : (prefixWord ++ tailWord_3560492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560492).length < 2 ^ (prefixWord ++ tailWord_3560492).sum := by decide
  have hdescent : baseEnd_3560492 < baseStart_3560492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560519 : List Nat := [1, 1, 4, 1, 3, 2, 2, 1, 2, 1, 5]
def baseStart_3560519 : Nat := 118140960795 + 3560519 * 2 ^ 59
def prefixEnd_3560519 : Nat := 4983230072969 + 3 ^ 40 * 3560519 * 2
def baseEnd_3560519 : Nat := 1828257626465860186737977

theorem tailTrace_3560519 : CollatzResearch.WordTrace tailWord_3560519 prefixEnd_3560519 1828257626465860186737977 := by
  unfold tailWord_3560519
  simp only [CollatzResearch.WordTrace]
  refine ⟨129862796587855226077932611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86575197725236817385288407 129862796587855226077932611)
  ·
    refine ⟨194794194881782839116898917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129862796587855226077932611 194794194881782839116898917)
    ·
      refine ⟨36523911540334282334418547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194794194881782839116898917 36523911540334282334418547)
      ·
        refine ⟨54785867310501423501627821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36523911540334282334418547 54785867310501423501627821)
        ·
          refine ⟨20544700241438033813110433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54785867310501423501627821 20544700241438033813110433)
          ·
            refine ⟨15408525181078525359832825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20544700241438033813110433 15408525181078525359832825)
            ·
              refine ⟨11556393885808894019874619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15408525181078525359832825 11556393885808894019874619)
              ·
                refine ⟨17334590828713341029811929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11556393885808894019874619 17334590828713341029811929)
                ·
                  refine ⟨13000943121535005772358947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17334590828713341029811929 13000943121535005772358947)
                  ·
                    refine ⟨19501414682302508658538421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13000943121535005772358947 19501414682302508658538421)
                    ·
                      refine ⟨1828257626465860186737977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19501414682302508658538421 1828257626465860186737977)
                      ·
                        rfl

theorem cell23_3560519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_3560519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3560519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3560519 prefixEnd_3560519 := by exact prefixLift 3560519
  have htrace : WordTrace (prefixWord ++ tailWord_3560519) baseStart_3560519 baseEnd_3560519 := by
    simpa [prefixWord, tailWord_3560519, baseEnd_3560519] using wordTrace_append hprefix tailTrace_3560519
  have hstable : (prefixWord ++ tailWord_3560519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560519).length < 2 ^ (prefixWord ++ tailWord_3560519).sum := by decide
  have hdescent : baseEnd_3560519 < baseStart_3560519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560546 : List Nat := [3, 3, 2, 2, 1, 1, 1, 1, 1, 4, 4]
def baseStart_3560546 : Nat := 118140960795 + 3560546 * 2 ^ 59
def prefixEnd_3560546 : Nat := 4983230072969 + 3 ^ 40 * 3560546 * 2
def baseEnd_3560546 : Nat := 1828271490443531581100353

theorem tailTrace_3560546 : CollatzResearch.WordTrace tailWord_3560546 prefixEnd_3560546 1828271490443531581100353 := by
  unfold tailWord_3560546
  simp only [CollatzResearch.WordTrace]
  refine ⟨32465945339689352422291373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86575854239171606459443661 32465945339689352422291373)
  ·
    refine ⟨12174729502383507158359265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32465945339689352422291373 12174729502383507158359265)
    ·
      refine ⟨9131047126787630368769449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12174729502383507158359265 9131047126787630368769449)
      ·
        refine ⟨6848285345090722776577087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9131047126787630368769449 6848285345090722776577087)
        ·
          refine ⟨10272428017636084164865631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6848285345090722776577087 10272428017636084164865631)
          ·
            refine ⟨15408642026454126247298447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10272428017636084164865631 15408642026454126247298447)
            ·
              refine ⟨23112963039681189370947671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15408642026454126247298447 23112963039681189370947671)
              ·
                refine ⟨34669444559521784056421507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23112963039681189370947671 34669444559521784056421507)
                ·
                  refine ⟨52004166839282676084632261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34669444559521784056421507 52004166839282676084632261)
                  ·
                    refine ⟨9750781282365501765868549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52004166839282676084632261 9750781282365501765868549)
                    ·
                      refine ⟨1828271490443531581100353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9750781282365501765868549 1828271490443531581100353)
                      ·
                        rfl

theorem cell23_3560546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_3560546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3560546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3560546 prefixEnd_3560546 := by exact prefixLift 3560546
  have htrace : WordTrace (prefixWord ++ tailWord_3560546) baseStart_3560546 baseEnd_3560546 := by
    simpa [prefixWord, tailWord_3560546, baseEnd_3560546] using wordTrace_append hprefix tailTrace_3560546
  have hstable : (prefixWord ++ tailWord_3560546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560546).length < 2 ^ (prefixWord ++ tailWord_3560546).sum := by decide
  have hdescent : baseEnd_3560546 < baseStart_3560546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560566 : List Nat := [5, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3]
def baseStart_3560566 : Nat := 118140960795 + 3560566 * 2 ^ 59
def prefixEnd_3560566 : Nat := 4983230072969 + 3 ^ 40 * 3560566 * 2
def baseEnd_3560566 : Nat := 1828281760056621502850261

theorem tailTrace_3560566 : CollatzResearch.WordTrace tailWord_3560566 prefixEnd_3560566 1828281760056621502850261 := by
  unfold tailWord_3560566
  simp only [CollatzResearch.WordTrace]
  refine ⟨8116531926167809569055847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86576340545789968736595701 8116531926167809569055847)
  ·
    refine ⟨12174797889251714353583771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8116531926167809569055847 12174797889251714353583771)
    ·
      refine ⟨18262196833877571530375657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12174797889251714353583771 18262196833877571530375657)
      ·
        refine ⟨13696647625408178647781743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18262196833877571530375657 13696647625408178647781743)
        ·
          refine ⟨20544971438112267971672615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13696647625408178647781743 20544971438112267971672615)
          ·
            refine ⟨30817457157168401957508923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20544971438112267971672615 30817457157168401957508923)
            ·
              refine ⟨46226185735752602936263385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30817457157168401957508923 46226185735752602936263385)
              ·
                refine ⟨34669639301814452202197539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46226185735752602936263385 34669639301814452202197539)
                ·
                  refine ⟨52004458952721678303296309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34669639301814452202197539 52004458952721678303296309)
                  ·
                    refine ⟨4875418026817657340934029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52004458952721678303296309 4875418026817657340934029)
                    ·
                      refine ⟨1828281760056621502850261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4875418026817657340934029 1828281760056621502850261)
                      ·
                        rfl

theorem cell23_3560566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_3560566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3560566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3560566 prefixEnd_3560566 := by exact prefixLift 3560566
  have htrace : WordTrace (prefixWord ++ tailWord_3560566) baseStart_3560566 baseEnd_3560566 := by
    simpa [prefixWord, tailWord_3560566, baseEnd_3560566] using wordTrace_append hprefix tailTrace_3560566
  have hstable : (prefixWord ++ tailWord_3560566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560566).length < 2 ^ (prefixWord ++ tailWord_3560566).sum := by decide
  have hdescent : baseEnd_3560566 < baseStart_3560566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560584 : List Nat := [2, 1, 3, 4, 3, 1, 1, 2, 2, 2, 2]
def baseStart_3560584 : Nat := 118140960795 + 3560584 * 2 ^ 59
def prefixEnd_3560584 : Nat := 4983230072969 + 3 ^ 40 * 3560584 * 2
def baseEnd_3560584 : Nat := 1828291002708402432425179

theorem tailTrace_3560584 : CollatzResearch.WordTrace tailWord_3560584 prefixEnd_3560584 1828291002708402432425179 := by
  unfold tailWord_3560584
  simp only [CollatzResearch.WordTrace]
  refine ⟨64932583666309871089524403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86576778221746494786032537 64932583666309871089524403)
  ·
    refine ⟨97398875499464806634286605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64932583666309871089524403 97398875499464806634286605)
    ·
      refine ⟨36524578312299302487857477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97398875499464806634286605 36524578312299302487857477)
      ·
        refine ⟨6848358433556119216473277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36524578312299302487857477 6848358433556119216473277)
        ·
          refine ⟨2568134412583544706177479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6848358433556119216473277 2568134412583544706177479)
          ·
            refine ⟨3852201618875317059266219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2568134412583544706177479 3852201618875317059266219)
            ·
              refine ⟨5778302428312975588899329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3852201618875317059266219 5778302428312975588899329)
              ·
                refine ⟨4333726821234731691674497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5778302428312975588899329 4333726821234731691674497)
                ·
                  refine ⟨3250295115926048768755873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4333726821234731691674497 3250295115926048768755873)
                  ·
                    refine ⟨2437721336944536576566905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3250295115926048768755873 2437721336944536576566905)
                    ·
                      refine ⟨1828291002708402432425179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2437721336944536576566905 1828291002708402432425179)
                      ·
                        rfl

theorem cell23_3560584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_3560584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3560584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3560584 prefixEnd_3560584 := by exact prefixLift 3560584
  have htrace : WordTrace (prefixWord ++ tailWord_3560584) baseStart_3560584 baseEnd_3560584 := by
    simpa [prefixWord, tailWord_3560584, baseEnd_3560584] using wordTrace_append hprefix tailTrace_3560584
  have hstable : (prefixWord ++ tailWord_3560584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560584).length < 2 ^ (prefixWord ++ tailWord_3560584).sum := by decide
  have hdescent : baseEnd_3560584 < baseStart_3560584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560626 : List Nat := [3, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3]
def baseStart_3560626 : Nat := 118140960795 + 3560626 * 2 ^ 59
def prefixEnd_3560626 : Nat := 4983230072969 + 3 ^ 40 * 3560626 * 2
def baseEnd_3560626 : Nat := 1828312568895891268099985

theorem tailTrace_3560626 : CollatzResearch.WordTrace tailWord_3560626 prefixEnd_3560626 1828312568895891268099985 := by
  unfold tailWord_3560626
  simp only [CollatzResearch.WordTrace]
  refine ⟨32466674799616895838019433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86577799465645055568051821 32466674799616895838019433)
  ·
    refine ⟨24350006099712671878514575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32466674799616895838019433 24350006099712671878514575)
    ·
      refine ⟨36525009149569007817771863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24350006099712671878514575 36525009149569007817771863)
      ·
        refine ⟨54787513724353511726657795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36525009149569007817771863 54787513724353511726657795)
        ·
          refine ⟨82181270586530267589986693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54787513724353511726657795 82181270586530267589986693)
          ·
            refine ⟨15408988234974425173122505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82181270586530267589986693 15408988234974425173122505)
            ·
              refine ⟨11556741176230818879841879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15408988234974425173122505 11556741176230818879841879)
              ·
                refine ⟨17335111764346228319762819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11556741176230818879841879 17335111764346228319762819)
                ·
                  refine ⟨26002667646519342479644229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17335111764346228319762819 26002667646519342479644229)
                  ·
                    refine ⟨4875500183722376714933293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26002667646519342479644229 4875500183722376714933293)
                    ·
                      refine ⟨1828312568895891268099985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4875500183722376714933293 1828312568895891268099985)
                      ·
                        rfl

theorem cell23_3560626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3].length) (baseStart_3560626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3560626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3560626 prefixEnd_3560626 := by exact prefixLift 3560626
  have htrace : WordTrace (prefixWord ++ tailWord_3560626) baseStart_3560626 baseEnd_3560626 := by
    simpa [prefixWord, tailWord_3560626, baseEnd_3560626] using wordTrace_append hprefix tailTrace_3560626
  have hstable : (prefixWord ++ tailWord_3560626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560626).length < 2 ^ (prefixWord ++ tailWord_3560626).sum := by decide
  have hdescent : baseEnd_3560626 < baseStart_3560626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560659 : List Nat := [1, 1, 1, 2, 1, 1, 1, 5, 5, 5]
def baseStart_3560659 : Nat := 118140960795 + 3560659 * 2 ^ 59
def prefixEnd_3560659 : Nat := 4983230072969 + 3 ^ 40 * 3560659 * 2
def baseEnd_3560659 : Nat := 609443171252496546329111

theorem tailTrace_3560659 : CollatzResearch.WordTrace tailWord_3560659 prefixEnd_3560659 609443171252496546329111 := by
  unfold tailWord_3560659
  simp only [CollatzResearch.WordTrace]
  refine ⟨129867902807348029988029031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86578601871565353325352687 129867902807348029988029031)
  ·
    refine ⟨194801854211022044982043547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129867902807348029988029031 194801854211022044982043547)
    ·
      refine ⟨292202781316533067473065321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194801854211022044982043547 292202781316533067473065321)
      ·
        refine ⟨219152085987399800604798991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292202781316533067473065321 219152085987399800604798991)
        ·
          refine ⟨328728128981099700907198487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219152085987399800604798991 328728128981099700907198487)
          ·
            refine ⟨493092193471649551360797731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328728128981099700907198487 493092193471649551360797731)
            ·
              refine ⟨739638290207474327041196597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 493092193471649551360797731 739638290207474327041196597)
              ·
                refine ⟨69341089706950718160112181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 739638290207474327041196597 69341089706950718160112181)
                ·
                  refine ⟨6500727160026629827510517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69341089706950718160112181 6500727160026629827510517)
                  ·
                    refine ⟨609443171252496546329111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6500727160026629827510517 609443171252496546329111)
                    ·
                      rfl

theorem cell23_3560659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 5, 5].length) (baseStart_3560659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3560659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3560659 prefixEnd_3560659 := by exact prefixLift 3560659
  have htrace : WordTrace (prefixWord ++ tailWord_3560659) baseStart_3560659 baseEnd_3560659 := by
    simpa [prefixWord, tailWord_3560659, baseEnd_3560659] using wordTrace_append hprefix tailTrace_3560659
  have hstable : (prefixWord ++ tailWord_3560659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560659).length < 2 ^ (prefixWord ++ tailWord_3560659).sum := by decide
  have hdescent : baseEnd_3560659 < baseStart_3560659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560683 : List Nat := [1, 1, 1, 1, 2, 6, 1, 3, 2, 3, 2]
def baseStart_3560683 : Nat := 118140960795 + 3560683 * 2 ^ 59
def prefixEnd_3560683 : Nat := 4983230072969 + 3 ^ 40 * 3560683 * 2
def baseEnd_3560683 : Nat := 1828341837293197545087223

theorem tailTrace_3560683 : CollatzResearch.WordTrace tailWord_3560683 prefixEnd_3560683 1828341837293197545087223 := by
  unfold tailWord_3560683
  simp only [CollatzResearch.WordTrace]
  refine ⟨129868778159261082086902703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86579185439507388057935135 129868778159261082086902703)
  ·
    refine ⟨194803167238891623130354055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129868778159261082086902703 194803167238891623130354055)
    ·
      refine ⟨292204750858337434695531083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194803167238891623130354055 292204750858337434695531083)
      ·
        refine ⟨438307126287506152043296625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292204750858337434695531083 438307126287506152043296625)
        ·
          refine ⟨328730344715629614032472469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 438307126287506152043296625 328730344715629614032472469)
          ·
            refine ⟨15409234908545138157772147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 328730344715629614032472469 15409234908545138157772147)
            ·
              refine ⟨23113852362817707236658221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15409234908545138157772147 23113852362817707236658221)
              ·
                refine ⟨8667694636056640213746833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23113852362817707236658221 8667694636056640213746833)
                ·
                  refine ⟨6500770977042480160310125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8667694636056640213746833 6500770977042480160310125)
                  ·
                    refine ⟨2437789116390930060116297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6500770977042480160310125 2437789116390930060116297)
                    ·
                      refine ⟨1828341837293197545087223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2437789116390930060116297 1828341837293197545087223)
                      ·
                        rfl

theorem cell23_3560683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3, 2, 3, 2].length) (baseStart_3560683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3560683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3560683 prefixEnd_3560683 := by exact prefixLift 3560683
  have htrace : WordTrace (prefixWord ++ tailWord_3560683) baseStart_3560683 baseEnd_3560683 := by
    simpa [prefixWord, tailWord_3560683, baseEnd_3560683] using wordTrace_append hprefix tailTrace_3560683
  have hstable : (prefixWord ++ tailWord_3560683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560683).length < 2 ^ (prefixWord ++ tailWord_3560683).sum := by decide
  have hdescent : baseEnd_3560683 < baseStart_3560683 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560707 : List Nat := [1, 1, 1, 3, 2, 4, 4, 2, 1, 1, 3]
def baseStart_3560707 : Nat := 118140960795 + 3560707 * 2 ^ 59
def prefixEnd_3560707 : Nat := 4983230072969 + 3 ^ 40 * 3560707 * 2
def baseEnd_3560707 : Nat := 1828354160828905451187113

theorem tailTrace_3560707 : CollatzResearch.WordTrace tailWord_3560707 prefixEnd_3560707 1828354160828905451187113 := by
  unfold tailWord_3560707
  simp only [CollatzResearch.WordTrace]
  refine ⟨129869653511174134185776375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86579769007449422790517583 129869653511174134185776375)
  ·
    refine ⟨194804480266761201278664563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129869653511174134185776375 194804480266761201278664563)
    ·
      refine ⟨292206720400141801917996845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194804480266761201278664563 292206720400141801917996845)
      ·
        refine ⟨109577520150053175719248817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 292206720400141801917996845 109577520150053175719248817)
        ·
          refine ⟨82183140112539881789436613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109577520150053175719248817 82183140112539881789436613)
          ·
            refine ⟨15409338771101227835519365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82183140112539881789436613 15409338771101227835519365)
            ·
              refine ⟨2889251019581480219159881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15409338771101227835519365 2889251019581480219159881)
              ·
                refine ⟨2166938264686110164369911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2889251019581480219159881 2166938264686110164369911)
                ·
                  refine ⟨3250407397029165246554867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2166938264686110164369911 3250407397029165246554867)
                  ·
                    refine ⟨4875611095543747869832301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3250407397029165246554867 4875611095543747869832301)
                    ·
                      refine ⟨1828354160828905451187113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4875611095543747869832301 1828354160828905451187113)
                      ·
                        rfl

theorem cell23_3560707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 2, 1, 1, 3].length) (baseStart_3560707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3560707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3560707 prefixEnd_3560707 := by exact prefixLift 3560707
  have htrace : WordTrace (prefixWord ++ tailWord_3560707) baseStart_3560707 baseEnd_3560707 := by
    simpa [prefixWord, tailWord_3560707, baseEnd_3560707] using wordTrace_append hprefix tailTrace_3560707
  have hstable : (prefixWord ++ tailWord_3560707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560707).length < 2 ^ (prefixWord ++ tailWord_3560707).sum := by decide
  have hdescent : baseEnd_3560707 < baseStart_3560707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560729 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 4, 2, 7]
def baseStart_3560729 : Nat := 118140960795 + 3560729 * 2 ^ 59
def prefixEnd_3560729 : Nat := 4983230072969 + 3 ^ 40 * 3560729 * 2
def baseEnd_3560729 : Nat := 1828365457403304365112011

theorem tailTrace_3560729 : CollatzResearch.WordTrace tailWord_3560729 prefixEnd_3560729 1828365457403304365112011 := by
  unfold tailWord_3560729
  simp only [CollatzResearch.WordTrace]
  refine ⟨129870455917094431943077241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86580303944729621295384827 129870455917094431943077241)
  ·
    refine ⟨97402841937820823957307931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129870455917094431943077241 97402841937820823957307931)
    ·
      refine ⟨146104262906731235935961897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97402841937820823957307931 146104262906731235935961897)
      ·
        refine ⟨109578197180048426951971423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146104262906731235935961897 109578197180048426951971423)
        ·
          refine ⟨164367295770072640427957135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109578197180048426951971423 164367295770072640427957135)
          ·
            refine ⟨246550943655108960641935703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164367295770072640427957135 246550943655108960641935703)
            ·
              refine ⟨369826415482663440962903555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246550943655108960641935703 369826415482663440962903555)
              ·
                refine ⟨554739623223995161444355333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 369826415482663440962903555 554739623223995161444355333)
                ·
                  refine ⟨104013679354499092770816625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 554739623223995161444355333 104013679354499092770816625)
                  ·
                    refine ⟨78010259515874319578112469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 104013679354499092770816625 78010259515874319578112469)
                    ·
                      refine ⟨1828365457403304365112011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 78010259515874319578112469 1828365457403304365112011)
                      ·
                        rfl

theorem cell23_3560729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 2, 7].length) (baseStart_3560729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3560729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3560729 prefixEnd_3560729 := by exact prefixLift 3560729
  have htrace : WordTrace (prefixWord ++ tailWord_3560729) baseStart_3560729 baseEnd_3560729 := by
    simpa [prefixWord, tailWord_3560729, baseEnd_3560729] using wordTrace_append hprefix tailTrace_3560729
  have hstable : (prefixWord ++ tailWord_3560729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560729).length < 2 ^ (prefixWord ++ tailWord_3560729).sum := by decide
  have hdescent : baseEnd_3560729 < baseStart_3560729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560730 : List Nat := [3, 1, 1, 3, 3, 1, 1, 1, 5, 2, 2]
def baseStart_3560730 : Nat := 118140960795 + 3560730 * 2 ^ 59
def prefixEnd_3560730 : Nat := 4983230072969 + 3 ^ 40 * 3560730 * 2
def baseEnd_3560730 : Nat := 1828365970883958861199507

theorem tailTrace_3560730 : CollatzResearch.WordTrace tailWord_3560730 prefixEnd_3560730 1828365970883958861199507 := by
  unfold tailWord_3560730
  simp only [CollatzResearch.WordTrace]
  refine ⟨32467623097522702278465911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86580328260060539409242429 32467623097522702278465911)
  ·
    refine ⟨48701434646284053417698867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32467623097522702278465911 48701434646284053417698867)
    ·
      refine ⟨73052151969426080126548301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48701434646284053417698867 73052151969426080126548301)
      ·
        refine ⟨27394556988534780047455613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73052151969426080126548301 27394556988534780047455613)
        ·
          refine ⟨10272958870700542517795855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27394556988534780047455613 10272958870700542517795855)
          ·
            refine ⟨15409438306050813776693783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10272958870700542517795855 15409438306050813776693783)
            ·
              refine ⟨23114157459076220665040675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15409438306050813776693783 23114157459076220665040675)
              ·
                refine ⟨34671236188614330997561013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23114157459076220665040675 34671236188614330997561013)
                ·
                  refine ⟨3250428392682593531021345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34671236188614330997561013 3250428392682593531021345)
                  ·
                    refine ⟨2437821294511945148266009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3250428392682593531021345 2437821294511945148266009)
                    ·
                      refine ⟨1828365970883958861199507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2437821294511945148266009 1828365970883958861199507)
                      ·
                        rfl

theorem cell23_3560730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 5, 2, 2].length) (baseStart_3560730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3560730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3560730 prefixEnd_3560730 := by exact prefixLift 3560730
  have htrace : WordTrace (prefixWord ++ tailWord_3560730) baseStart_3560730 baseEnd_3560730 := by
    simpa [prefixWord, tailWord_3560730, baseEnd_3560730] using wordTrace_append hprefix tailTrace_3560730
  have hstable : (prefixWord ++ tailWord_3560730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560730).length < 2 ^ (prefixWord ++ tailWord_3560730).sum := by decide
  have hdescent : baseEnd_3560730 < baseStart_3560730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560773 : List Nat := [1, 3, 1, 1, 1, 2, 1, 3, 5, 3, 2]
def baseStart_3560773 : Nat := 118140960795 + 3560773 * 2 ^ 59
def prefixEnd_3560773 : Nat := 4983230072969 + 3 ^ 40 * 3560773 * 2
def baseEnd_3560773 : Nat := 1828388050552102192961809

theorem tailTrace_3560773 : CollatzResearch.WordTrace tailWord_3560773 prefixEnd_3560773 1828388050552102192961809 := by
  unfold tailWord_3560773
  simp only [CollatzResearch.WordTrace]
  refine ⟨129872060728935027457678973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86581373819290018305119315 129872060728935027457678973)
  ·
    refine ⟨48702022773350635296629615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129872060728935027457678973 48702022773350635296629615)
    ·
      refine ⟨73053034160025952944944423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48702022773350635296629615 73053034160025952944944423)
      ·
        refine ⟨109579551240038929417416635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73053034160025952944944423 109579551240038929417416635)
        ·
          refine ⟨164369326860058394126124953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109579551240038929417416635 164369326860058394126124953)
          ·
            refine ⟨123276995145043795594593715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164369326860058394126124953 123276995145043795594593715)
            ·
              refine ⟨184915492717565693391890573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123276995145043795594593715 184915492717565693391890573)
              ·
                refine ⟨69343309769087135021958965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 184915492717565693391890573 69343309769087135021958965)
                ·
                  refine ⟨6500935290851918908308653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69343309769087135021958965 6500935290851918908308653)
                  ·
                    refine ⟨2437850734069469590615745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6500935290851918908308653 2437850734069469590615745)
                    ·
                      refine ⟨1828388050552102192961809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2437850734069469590615745 1828388050552102192961809)
                      ·
                        rfl

theorem cell23_3560773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 5, 3, 2].length) (baseStart_3560773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3560773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3560773 prefixEnd_3560773 := by exact prefixLift 3560773
  have htrace : WordTrace (prefixWord ++ tailWord_3560773) baseStart_3560773 baseEnd_3560773 := by
    simpa [prefixWord, tailWord_3560773, baseEnd_3560773] using wordTrace_append hprefix tailTrace_3560773
  have hstable : (prefixWord ++ tailWord_3560773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560773).length < 2 ^ (prefixWord ++ tailWord_3560773).sum := by decide
  have hdescent : baseEnd_3560773 < baseStart_3560773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560774 : List Nat := [6, 1, 1, 3, 1, 2, 1, 1, 1, 6]
def baseStart_3560774 : Nat := 118140960795 + 3560774 * 2 ^ 59
def prefixEnd_3560774 : Nat := 4983230072969 + 3 ^ 40 * 3560774 * 2
def baseEnd_3560774 : Nat := 609462854677585563016435

theorem tailTrace_3560774 : CollatzResearch.WordTrace tailWord_3560774 prefixEnd_3560774 609462854677585563016435 := by
  unfold tailWord_3560774
  simp only [CollatzResearch.WordTrace]
  refine ⟨4058503037560356394639543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 86581398134620936418976917 4058503037560356394639543)
  ·
    refine ⟨6087754556340534591959315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4058503037560356394639543 6087754556340534591959315)
    ·
      refine ⟨9131631834510801887938973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6087754556340534591959315 9131631834510801887938973)
      ·
        refine ⟨3424361937941550707977115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9131631834510801887938973 3424361937941550707977115)
        ·
          refine ⟨5136542906912326061965673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3424361937941550707977115 5136542906912326061965673)
          ·
            refine ⟨3852407180184244546474255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5136542906912326061965673 3852407180184244546474255)
            ·
              refine ⟨5778610770276366819711383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3852407180184244546474255 5778610770276366819711383)
              ·
                refine ⟨8667916155414550229567075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5778610770276366819711383 8667916155414550229567075)
                ·
                  refine ⟨13001874233121825344350613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8667916155414550229567075 13001874233121825344350613)
                  ·
                    refine ⟨609462854677585563016435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13001874233121825344350613 609462854677585563016435)
                    ·
                      rfl

theorem cell23_3560774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_3560774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3560774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3560774 prefixEnd_3560774 := by exact prefixLift 3560774
  have htrace : WordTrace (prefixWord ++ tailWord_3560774) baseStart_3560774 baseEnd_3560774 := by
    simpa [prefixWord, tailWord_3560774, baseEnd_3560774] using wordTrace_append hprefix tailTrace_3560774
  have hstable : (prefixWord ++ tailWord_3560774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560774).length < 2 ^ (prefixWord ++ tailWord_3560774).sum := by decide
  have hdescent : baseEnd_3560774 < baseStart_3560774 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560780 : List Nat := [2, 2, 1, 3, 2, 4, 1, 1, 1, 3, 3]
def baseStart_3560780 : Nat := 118140960795 + 3560780 * 2 ^ 59
def prefixEnd_3560780 : Nat := 4983230072969 + 3 ^ 40 * 3560780 * 2
def baseEnd_3560780 : Nat := 1828391644916683665574277

theorem tailTrace_3560780 : CollatzResearch.WordTrace tailWord_3560780 prefixEnd_3560780 1828391644916683665574277 := by
  unfold tailWord_3560780
  simp only [CollatzResearch.WordTrace]
  refine ⟨64936158019954833826591897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86581544026606445102122529 64936158019954833826591897)
  ·
    refine ⟨48702118514966125369943923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64936158019954833826591897 48702118514966125369943923)
    ·
      refine ⟨73053177772449188054915885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48702118514966125369943923 73053177772449188054915885)
      ·
        refine ⟨27394941664668445520593457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73053177772449188054915885 27394941664668445520593457)
        ·
          refine ⟨20546206248501334140445093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27394941664668445520593457 20546206248501334140445093)
          ·
            refine ⟨3852413671594000151333455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20546206248501334140445093 3852413671594000151333455)
            ·
              refine ⟨5778620507391000227000183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3852413671594000151333455 5778620507391000227000183)
              ·
                refine ⟨8667930761086500340500275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5778620507391000227000183 8667930761086500340500275)
                ·
                  refine ⟨13001896141629750510750413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8667930761086500340500275 13001896141629750510750413)
                  ·
                    refine ⟨4875711053111156441531405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13001896141629750510750413 4875711053111156441531405)
                    ·
                      refine ⟨1828391644916683665574277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4875711053111156441531405 1828391644916683665574277)
                      ·
                        rfl

theorem cell23_3560780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_3560780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3560780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3560780 prefixEnd_3560780 := by exact prefixLift 3560780
  have htrace : WordTrace (prefixWord ++ tailWord_3560780) baseStart_3560780 baseEnd_3560780 := by
    simpa [prefixWord, tailWord_3560780, baseEnd_3560780] using wordTrace_append hprefix tailTrace_3560780
  have hstable : (prefixWord ++ tailWord_3560780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560780).length < 2 ^ (prefixWord ++ tailWord_3560780).sum := by decide
  have hdescent : baseEnd_3560780 < baseStart_3560780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560877 : List Nat := [1, 5, 2, 2, 1, 2, 1, 4, 5]
def baseStart_3560877 : Nat := 118140960795 + 3560877 * 2 ^ 59
def prefixEnd_3560877 : Nat := 4983230072969 + 3 ^ 40 * 3560877 * 2
def baseEnd_3560877 : Nat := 203160161393352198451259

theorem tailTrace_3560877 : CollatzResearch.WordTrace tailWord_3560877 prefixEnd_3560877 203160161393352198451259 := by
  unfold tailWord_3560877
  simp only [CollatzResearch.WordTrace]
  refine ⟨129875853920558253219464885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86583902613705502146309923 129875853920558253219464885)
  ·
    refine ⟨12175861305052336239324833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 129875853920558253219464885 12175861305052336239324833)
    ·
      refine ⟨9131895978789252179493625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12175861305052336239324833 9131895978789252179493625)
      ·
        refine ⟨6848921984091939134620219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9131895978789252179493625 6848921984091939134620219)
        ·
          refine ⟨10273382976137908701930329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6848921984091939134620219 10273382976137908701930329)
          ·
            refine ⟨7705037232103431526447747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10273382976137908701930329 7705037232103431526447747)
            ·
              refine ⟨11557555848155147289671621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7705037232103431526447747 11557555848155147289671621)
              ·
                refine ⟨2167041721529090116813429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11557555848155147289671621 2167041721529090116813429)
                ·
                  refine ⟨203160161393352198451259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2167041721529090116813429 203160161393352198451259)
                  ·
                    rfl

theorem cell23_3560877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 4, 5].length) (baseStart_3560877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3560877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3560877 prefixEnd_3560877 := by exact prefixLift 3560877
  have htrace : WordTrace (prefixWord ++ tailWord_3560877) baseStart_3560877 baseEnd_3560877 := by
    simpa [prefixWord, tailWord_3560877, baseEnd_3560877] using wordTrace_append hprefix tailTrace_3560877
  have hstable : (prefixWord ++ tailWord_3560877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560877).length < 2 ^ (prefixWord ++ tailWord_3560877).sum := by decide
  have hdescent : baseEnd_3560877 < baseStart_3560877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560893 : List Nat := [1, 4, 1, 2, 2, 1, 2, 2, 1, 3, 4]
def baseStart_3560893 : Nat := 118140960795 + 3560893 * 2 ^ 59
def prefixEnd_3560893 : Nat := 4983230072969 + 3 ^ 40 * 3560893 * 2
def baseEnd_3560893 : Nat := 1828449668230641723461257

theorem tailTrace_3560893 : CollatzResearch.WordTrace tailWord_3560893 prefixEnd_3560893 1828449668230641723461257 := by
  unfold tailWord_3560893
  simp only [CollatzResearch.WordTrace]
  refine ⟨129876437488500287952047333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86584291659000191968031555 129876437488500287952047333)
  ·
    refine ⟨24351832029093803991008875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129876437488500287952047333 24351832029093803991008875)
    ·
      refine ⟨36527748043640705986513313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24351832029093803991008875 36527748043640705986513313)
      ·
        refine ⟨27395811032730529489884985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36527748043640705986513313 27395811032730529489884985)
        ·
          refine ⟨20546858274547897117413739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27395811032730529489884985 20546858274547897117413739)
          ·
            refine ⟨30820287411821845676120609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20546858274547897117413739 30820287411821845676120609)
            ·
              refine ⟨23115215558866384257090457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30820287411821845676120609 23115215558866384257090457)
              ·
                refine ⟨17336411669149788192817843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23115215558866384257090457 17336411669149788192817843)
                ·
                  refine ⟨26004617503724682289226765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17336411669149788192817843 26004617503724682289226765)
                  ·
                    refine ⟨9751731563896755858460037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26004617503724682289226765 9751731563896755858460037)
                    ·
                      refine ⟨1828449668230641723461257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9751731563896755858460037 1828449668230641723461257)
                      ·
                        rfl

theorem cell23_3560893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_3560893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3560893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3560893 prefixEnd_3560893 := by exact prefixLift 3560893
  have htrace : WordTrace (prefixWord ++ tailWord_3560893) baseStart_3560893 baseEnd_3560893 := by
    simpa [prefixWord, tailWord_3560893, baseEnd_3560893] using wordTrace_append hprefix tailTrace_3560893
  have hstable : (prefixWord ++ tailWord_3560893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560893).length < 2 ^ (prefixWord ++ tailWord_3560893).sum := by decide
  have hdescent : baseEnd_3560893 < baseStart_3560893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560910 : List Nat := [4, 1, 1, 1, 2, 1, 5, 1, 2, 1, 4]
def baseStart_3560910 : Nat := 118140960795 + 3560910 * 2 ^ 59
def prefixEnd_3560910 : Nat := 4983230072969 + 3 ^ 40 * 3560910 * 2
def baseEnd_3560910 : Nat := 1828458397401768156948679

theorem tailTrace_3560910 : CollatzResearch.WordTrace tailWord_3560910 prefixEnd_3560910 1828458397401768156948679 := by
  unfold tailWord_3560910
  simp only [CollatzResearch.WordTrace]
  refine ⟨16234632191179837481927023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86584705019625799903610789 16234632191179837481927023)
  ·
    refine ⟨24351948286769756222890535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16234632191179837481927023 24351948286769756222890535)
    ·
      refine ⟨36527922430154634334335803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24351948286769756222890535 36527922430154634334335803)
      ·
        refine ⟨54791883645231951501503705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36527922430154634334335803 54791883645231951501503705)
        ·
          refine ⟨41093912733923963626127779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54791883645231951501503705 41093912733923963626127779)
          ·
            refine ⟨61640869100885945439191669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41093912733923963626127779 61640869100885945439191669)
            ·
              refine ⟨5778831478208057384924219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61640869100885945439191669 5778831478208057384924219)
              ·
                refine ⟨8668247217312086077386329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5778831478208057384924219 8668247217312086077386329)
                ·
                  refine ⟨6501185412984064558039747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8668247217312086077386329 6501185412984064558039747)
                  ·
                    refine ⟨9751778119476096837059621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6501185412984064558039747 9751778119476096837059621)
                    ·
                      refine ⟨1828458397401768156948679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9751778119476096837059621 1828458397401768156948679)
                      ·
                        rfl

theorem cell23_3560910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 1, 2, 1, 4].length) (baseStart_3560910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3560910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3560910 prefixEnd_3560910 := by exact prefixLift 3560910
  have htrace : WordTrace (prefixWord ++ tailWord_3560910) baseStart_3560910 baseEnd_3560910 := by
    simpa [prefixWord, tailWord_3560910, baseEnd_3560910] using wordTrace_append hprefix tailTrace_3560910
  have hstable : (prefixWord ++ tailWord_3560910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560910).length < 2 ^ (prefixWord ++ tailWord_3560910).sum := by decide
  have hdescent : baseEnd_3560910 < baseStart_3560910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560971 : List Nat := [1, 1, 1, 1, 9, 1, 1, 3, 1, 4]
def baseStart_3560971 : Nat := 118140960795 + 3560971 * 2 ^ 59
def prefixEnd_3560971 : Nat := 4983230072969 + 3 ^ 40 * 3560971 * 2
def baseEnd_3560971 : Nat := 609496573240564139428633

theorem tailTrace_3560971 : CollatzResearch.WordTrace tailWord_3560971 prefixEnd_3560971 609496573240564139428633 := by
  unfold tailWord_3560971
  simp only [CollatzResearch.WordTrace]
  refine ⟨129879282382217707273386767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86586188254811804848924511 129879282382217707273386767)
  ·
    refine ⟨194818923573326560910080151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129879282382217707273386767 194818923573326560910080151)
    ·
      refine ⟨292228385359989841365120227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194818923573326560910080151 292228385359989841365120227)
      ·
        refine ⟨438342578039984762047680341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292228385359989841365120227 438342578039984762047680341)
        ·
          refine ⟨2568413543203035715123127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 438342578039984762047680341 2568413543203035715123127)
          ·
            refine ⟨3852620314804553572684691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2568413543203035715123127 3852620314804553572684691)
            ·
              refine ⟨5778930472206830359027037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3852620314804553572684691 5778930472206830359027037)
              ·
                refine ⟨2167098927077561384635139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5778930472206830359027037 2167098927077561384635139)
                ·
                  refine ⟨3250648390616342076952709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2167098927077561384635139 3250648390616342076952709)
                  ·
                    refine ⟨609496573240564139428633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3250648390616342076952709 609496573240564139428633)
                    ·
                      rfl

theorem cell23_3560971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 3, 1, 4].length) (baseStart_3560971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3560971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3560971 prefixEnd_3560971 := by exact prefixLift 3560971
  have htrace : WordTrace (prefixWord ++ tailWord_3560971) baseStart_3560971 baseEnd_3560971 := by
    simpa [prefixWord, tailWord_3560971, baseEnd_3560971] using wordTrace_append hprefix tailTrace_3560971
  have hstable : (prefixWord ++ tailWord_3560971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560971).length < 2 ^ (prefixWord ++ tailWord_3560971).sum := by decide
  have hdescent : baseEnd_3560971 < baseStart_3560971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560994 : List Nat := [3, 3, 1, 1, 1, 1, 2, 6, 1, 1, 3]
def baseStart_3560994 : Nat := 118140960795 + 3560994 * 2 ^ 59
def prefixEnd_3560994 : Nat := 4983230072969 + 3 ^ 40 * 3560994 * 2
def baseEnd_3560994 : Nat := 1828501529776745828298293

theorem tailTrace_3560994 : CollatzResearch.WordTrace tailWord_3560994 prefixEnd_3560994 1828501529776745828298293 := by
  unfold tailWord_3560994
  simp only [CollatzResearch.WordTrace]
  refine ⟨32470030315283595550368509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86586747507422921467649357 32470030315283595550368509)
  ·
    refine ⟨12176261368231348331388191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32470030315283595550368509 12176261368231348331388191)
    ·
      refine ⟨18264392052347022497082287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12176261368231348331388191 18264392052347022497082287)
      ·
        refine ⟨27396588078520533745623431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18264392052347022497082287 27396588078520533745623431)
        ·
          refine ⟨41094882117780800618435147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27396588078520533745623431 41094882117780800618435147)
          ·
            refine ⟨61642323176671200927652721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41094882117780800618435147 61642323176671200927652721)
            ·
              refine ⟨46231742382503400695739541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61642323176671200927652721 46231742382503400695739541)
              ·
                refine ⟨2167112924179846907612791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46231742382503400695739541 2167112924179846907612791)
                ·
                  refine ⟨3250669386269770361419187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2167112924179846907612791 3250669386269770361419187)
                  ·
                    refine ⟨4876004079404655542128781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3250669386269770361419187 4876004079404655542128781)
                    ·
                      refine ⟨1828501529776745828298293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4876004079404655542128781 1828501529776745828298293)
                      ·
                        rfl

theorem cell23_3560994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 6, 1, 1, 3].length) (baseStart_3560994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3560994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3560994 prefixEnd_3560994 := by exact prefixLift 3560994
  have htrace : WordTrace (prefixWord ++ tailWord_3560994) baseStart_3560994 baseEnd_3560994 := by
    simpa [prefixWord, tailWord_3560994, baseEnd_3560994] using wordTrace_append hprefix tailTrace_3560994
  have hstable : (prefixWord ++ tailWord_3560994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560994).length < 2 ^ (prefixWord ++ tailWord_3560994).sum := by decide
  have hdescent : baseEnd_3560994 < baseStart_3560994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561003 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 1, 8, 3]
def baseStart_3561003 : Nat := 118140960795 + 3561003 * 2 ^ 59
def prefixEnd_3561003 : Nat := 4983230072969 + 3 ^ 40 * 3561003 * 2
def baseEnd_3561003 : Nat := 1828506151102636293085751

theorem tailTrace_3561003 : CollatzResearch.WordTrace tailWord_3561003 prefixEnd_3561003 1828506151102636293085751 := by
  unfold tailWord_3561003
  simp only [CollatzResearch.WordTrace]
  refine ⟨129880449518101776738551663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86586966345401184492367775 129880449518101776738551663)
  ·
    refine ⟨194820674277152665107827495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129880449518101776738551663 194820674277152665107827495)
    ·
      refine ⟨292231011415728997661741243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194820674277152665107827495 292231011415728997661741243)
      ·
        refine ⟨438346517123593496492611865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292231011415728997661741243 438346517123593496492611865)
        ·
          refine ⟨328759887842695122369458899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 438346517123593496492611865 328759887842695122369458899)
          ·
            refine ⟨493139831764042683554188349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328759887842695122369458899 493139831764042683554188349)
            ·
              refine ⟨184927436911516006332820631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 493139831764042683554188349 184927436911516006332820631)
              ·
                refine ⟨277391155367274009499230947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184927436911516006332820631 277391155367274009499230947)
                ·
                  refine ⟨416086733050911014248846421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 277391155367274009499230947 416086733050911014248846421)
                  ·
                    refine ⟨4876016402940363448228669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 416086733050911014248846421 4876016402940363448228669)
                    ·
                      refine ⟨1828506151102636293085751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4876016402940363448228669 1828506151102636293085751)
                      ·
                        rfl

theorem cell23_3561003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 8, 3].length) (baseStart_3561003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3561003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3561003 prefixEnd_3561003 := by exact prefixLift 3561003
  have htrace : WordTrace (prefixWord ++ tailWord_3561003) baseStart_3561003 baseEnd_3561003 := by
    simpa [prefixWord, tailWord_3561003, baseEnd_3561003] using wordTrace_append hprefix tailTrace_3561003
  have hstable : (prefixWord ++ tailWord_3561003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561003).length < 2 ^ (prefixWord ++ tailWord_3561003).sum := by decide
  have hdescent : baseEnd_3561003 < baseStart_3561003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561017 : List Nat := [1, 2, 1, 5, 1, 2, 3, 2, 1, 1, 4]
def baseStart_3561017 : Nat := 118140960795 + 3561017 * 2 ^ 59
def prefixEnd_3561017 : Nat := 4983230072969 + 3 ^ 40 * 3561017 * 2
def baseEnd_3561017 : Nat := 1828513339831799238310687

theorem tailTrace_3561017 : CollatzResearch.WordTrace tailWord_3561017 prefixEnd_3561017 1828513339831799238310687 := by
  unfold tailWord_3561017
  simp only [CollatzResearch.WordTrace]
  refine ⟨129880960140051057129561305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86587306760034038086374203 129880960140051057129561305)
  ·
    refine ⟨97410720105038292847170979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129880960140051057129561305 97410720105038292847170979)
    ·
      refine ⟨146116080157557439270756469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97410720105038292847170979 146116080157557439270756469)
      ·
        refine ⟨13698382514771009931633419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 146116080157557439270756469 13698382514771009931633419)
        ·
          refine ⟨20547573772156514897450129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13698382514771009931633419 20547573772156514897450129)
          ·
            refine ⟨15410680329117386173087597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20547573772156514897450129 15410680329117386173087597)
            ·
              refine ⟨5779005123419019814907849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15410680329117386173087597 5779005123419019814907849)
              ·
                refine ⟨4334253842564264861180887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5779005123419019814907849 4334253842564264861180887)
                ·
                  refine ⟨6501380763846397291771331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4334253842564264861180887 6501380763846397291771331)
                  ·
                    refine ⟨9752071145769595937656997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6501380763846397291771331 9752071145769595937656997)
                    ·
                      refine ⟨1828513339831799238310687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9752071145769595937656997 1828513339831799238310687)
                      ·
                        rfl

theorem cell23_3561017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_3561017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3561017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3561017 prefixEnd_3561017 := by exact prefixLift 3561017
  have htrace : WordTrace (prefixWord ++ tailWord_3561017) baseStart_3561017 baseEnd_3561017 := by
    simpa [prefixWord, tailWord_3561017, baseEnd_3561017] using wordTrace_append hprefix tailTrace_3561017
  have hstable : (prefixWord ++ tailWord_3561017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561017).length < 2 ^ (prefixWord ++ tailWord_3561017).sum := by decide
  have hdescent : baseEnd_3561017 < baseStart_3561017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561023 : List Nat := [1, 1, 2, 2, 3, 3, 2, 9]
def baseStart_3561023 : Nat := 118140960795 + 3561023 * 2 ^ 59
def prefixEnd_3561023 : Nat := 4983230072969 + 3 ^ 40 * 3561023 * 2
def baseEnd_3561023 : Nat := 67722830396878748697617

theorem tailTrace_3561023 : CollatzResearch.WordTrace tailWord_3561023 prefixEnd_3561023 67722830396878748697617 := by
  unfold tailWord_3561023
  simp only [CollatzResearch.WordTrace]
  refine ⟨129881178978029320154279723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86587452652019546769519815 129881178978029320154279723)
  ·
    refine ⟨194821768467043980231419585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129881178978029320154279723 194821768467043980231419585)
    ·
      refine ⟨146116326350282985173564689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194821768467043980231419585 146116326350282985173564689)
      ·
        refine ⟨109587244762712238880173517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146116326350282985173564689 109587244762712238880173517)
        ·
          refine ⟨41095216786017089580065069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109587244762712238880173517 41095216786017089580065069)
          ·
            refine ⟨15410706294756408592524401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41095216786017089580065069 15410706294756408592524401)
            ·
              refine ⟨11558029721067306444393301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15410706294756408592524401 11558029721067306444393301)
              ·
                refine ⟨67722830396878748697617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11558029721067306444393301 67722830396878748697617)
                ·
                  rfl

theorem cell23_3561023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 9].length) (baseStart_3561023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3561023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3561023 prefixEnd_3561023 := by exact prefixLift 3561023
  have htrace : WordTrace (prefixWord ++ tailWord_3561023) baseStart_3561023 baseEnd_3561023 := by
    simpa [prefixWord, tailWord_3561023, baseEnd_3561023] using wordTrace_append hprefix tailTrace_3561023
  have hstable : (prefixWord ++ tailWord_3561023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561023).length < 2 ^ (prefixWord ++ tailWord_3561023).sum := by decide
  have hdescent : baseEnd_3561023 < baseStart_3561023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561083 : List Nat := [1, 1, 1, 1, 1, 4, 3, 2, 1, 8]
def baseStart_3561083 : Nat := 118140960795 + 3561083 * 2 ^ 59
def prefixEnd_3561083 : Nat := 4983230072969 + 3 ^ 40 * 3561083 * 2
def baseEnd_3561083 : Nat := 609515743184998660028461

theorem tailTrace_3561083 : CollatzResearch.WordTrace tailWord_3561083 prefixEnd_3561083 609515743184998660028461 := by
  unfold tailWord_3561083
  simp only [CollatzResearch.WordTrace]
  refine ⟨129883367357811950401463903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86588911571874633600975935 129883367357811950401463903)
  ·
    refine ⟨194825051036717925602195855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129883367357811950401463903 194825051036717925602195855)
    ·
      refine ⟨292237576555076888403293783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194825051036717925602195855 292237576555076888403293783)
      ·
        refine ⟨438356364832615332604940675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292237576555076888403293783 438356364832615332604940675)
        ·
          refine ⟨657534547248922998907411013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 438356364832615332604940675 657534547248922998907411013)
          ·
            refine ⟨123287727609173062295139565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 657534547248922998907411013 123287727609173062295139565)
            ·
              refine ⟨46232897853439898360677337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123287727609173062295139565 46232897853439898360677337)
              ·
                refine ⟨34674673390079923770508003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46232897853439898360677337 34674673390079923770508003)
                ·
                  refine ⟨52012010085119885655762005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34674673390079923770508003 52012010085119885655762005)
                  ·
                    refine ⟨609515743184998660028461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 52012010085119885655762005 609515743184998660028461)
                    ·
                      rfl

theorem cell23_3561083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 8].length) (baseStart_3561083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3561083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3561083 prefixEnd_3561083 := by exact prefixLift 3561083
  have htrace : WordTrace (prefixWord ++ tailWord_3561083) baseStart_3561083 baseEnd_3561083 := by
    simpa [prefixWord, tailWord_3561083, baseEnd_3561083] using wordTrace_append hprefix tailTrace_3561083
  have hstable : (prefixWord ++ tailWord_3561083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561083).length < 2 ^ (prefixWord ++ tailWord_3561083).sum := by decide
  have hdescent : baseEnd_3561083 < baseStart_3561083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561103 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 6]
def baseStart_3561103 : Nat := 118140960795 + 3561103 * 2 ^ 59
def prefixEnd_3561103 : Nat := 4983230072969 + 3 ^ 40 * 3561103 * 2
def baseEnd_3561103 : Nat := 1828557499168085901835291

theorem tailTrace_3561103 : CollatzResearch.WordTrace tailWord_3561103 prefixEnd_3561103 1828557499168085901835291 := by
  unfold tailWord_3561103
  simp only [CollatzResearch.WordTrace]
  refine ⟨129884096817739493817191963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86589397878492995878127975 129884096817739493817191963)
  ·
    refine ⟨194826145226609240725787945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129884096817739493817191963 194826145226609240725787945)
    ·
      refine ⟨146119608919956930544340959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194826145226609240725787945 146119608919956930544340959)
      ·
        refine ⟨219179413379935395816511439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146119608919956930544340959 219179413379935395816511439)
        ·
          refine ⟨328769120069903093724767159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219179413379935395816511439 328769120069903093724767159)
          ·
            refine ⟨493153680104854640587150739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328769120069903093724767159 493153680104854640587150739)
            ·
              refine ⟨739730520157281960880726109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 493153680104854640587150739 739730520157281960880726109)
              ·
                refine ⟨277398945058980735330272291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 739730520157281960880726109 277398945058980735330272291)
                ·
                  refine ⟨416098417588471102995408437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 277398945058980735330272291 416098417588471102995408437)
                  ·
                    refine ⟨39009226648919165905819541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 416098417588471102995408437 39009226648919165905819541)
                    ·
                      refine ⟨1828557499168085901835291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39009226648919165905819541 1828557499168085901835291)
                      ·
                        rfl

theorem cell23_3561103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 6].length) (baseStart_3561103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3561103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3561103 prefixEnd_3561103 := by exact prefixLift 3561103
  have htrace : WordTrace (prefixWord ++ tailWord_3561103) baseStart_3561103 baseEnd_3561103 := by
    simpa [prefixWord, tailWord_3561103, baseEnd_3561103] using wordTrace_append hprefix tailTrace_3561103
  have hstable : (prefixWord ++ tailWord_3561103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561103).length < 2 ^ (prefixWord ++ tailWord_3561103).sum := by decide
  have hdescent : baseEnd_3561103 < baseStart_3561103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561118 : List Nat := [4, 3, 1, 1, 1, 3, 3, 1, 2, 1, 3]
def baseStart_3561118 : Nat := 118140960795 + 3561118 * 2 ^ 59
def prefixEnd_3561118 : Nat := 4983230072969 + 3 ^ 40 * 3561118 * 2
def baseEnd_3561118 : Nat := 1828565201377903343147723

theorem tailTrace_3561118 : CollatzResearch.WordTrace tailWord_3561118 prefixEnd_3561118 1828565201377903343147723 := by
  unfold tailWord_3561118
  simp only [CollatzResearch.WordTrace]
  refine ⟨16235580489085643922373501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86589762608456767585992005 16235580489085643922373501)
  ·
    refine ⟨6088342683407116470890063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16235580489085643922373501 6088342683407116470890063)
    ·
      refine ⟨9132514025110674706335095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6088342683407116470890063 9132514025110674706335095)
      ·
        refine ⟨13698771037666012059502643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9132514025110674706335095 13698771037666012059502643)
        ·
          refine ⟨20548156556499018089253965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13698771037666012059502643 20548156556499018089253965)
          ·
            refine ⟨7705558708687131783470237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20548156556499018089253965 7705558708687131783470237)
            ·
              refine ⟨2889584515757674418801339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7705558708687131783470237 2889584515757674418801339)
              ·
                refine ⟨4334376773636511628202009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2889584515757674418801339 4334376773636511628202009)
                ·
                  refine ⟨3250782580227383721151507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4334376773636511628202009 3250782580227383721151507)
                  ·
                    refine ⟨4876173870341075581727261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3250782580227383721151507 4876173870341075581727261)
                    ·
                      refine ⟨1828565201377903343147723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4876173870341075581727261 1828565201377903343147723)
                      ·
                        rfl

theorem cell23_3561118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_3561118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3561118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3561118 prefixEnd_3561118 := by exact prefixLift 3561118
  have htrace : WordTrace (prefixWord ++ tailWord_3561118) baseStart_3561118 baseEnd_3561118 := by
    simpa [prefixWord, tailWord_3561118, baseEnd_3561118] using wordTrace_append hprefix tailTrace_3561118
  have hstable : (prefixWord ++ tailWord_3561118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561118).length < 2 ^ (prefixWord ++ tailWord_3561118).sum := by decide
  have hdescent : baseEnd_3561118 < baseStart_3561118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561124 : List Nat := [2, 3, 1, 2, 2, 2, 3, 1, 1, 4, 2]
def baseStart_3561124 : Nat := 118140960795 + 3561124 * 2 ^ 59
def prefixEnd_3561124 : Nat := 4983230072969 + 3 ^ 40 * 3561124 * 2
def baseEnd_3561124 : Nat := 1828568282261830319672695

theorem tailTrace_3561124 : CollatzResearch.WordTrace tailWord_3561124 prefixEnd_3561124 1828568282261830319672695 := by
  unfold tailWord_3561124
  simp only [CollatzResearch.WordTrace]
  refine ⟨64942431375331707201853213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86589908500442276269137617 64942431375331707201853213)
  ·
    refine ⟨24353411765749390200694955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64942431375331707201853213 24353411765749390200694955)
    ·
      refine ⟨36530117648624085301042433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24353411765749390200694955 36530117648624085301042433)
      ·
        refine ⟨27397588236468063975781825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36530117648624085301042433 27397588236468063975781825)
        ·
          refine ⟨20548191177351047981836369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27397588236468063975781825 20548191177351047981836369)
          ·
            refine ⟨15411143383013285986377277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20548191177351047981836369 15411143383013285986377277)
            ·
              refine ⟨5779178768629982244891479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15411143383013285986377277 5779178768629982244891479)
              ·
                refine ⟨8668768152944973367337219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5779178768629982244891479 8668768152944973367337219)
                ·
                  refine ⟨13003152229417460051005829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8668768152944973367337219 13003152229417460051005829)
                  ·
                    refine ⟨2438091043015773759563593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13003152229417460051005829 2438091043015773759563593)
                    ·
                      refine ⟨1828568282261830319672695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2438091043015773759563593 1828568282261830319672695)
                      ·
                        rfl

theorem cell23_3561124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 1, 1, 4, 2].length) (baseStart_3561124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3561124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3561124 prefixEnd_3561124 := by exact prefixLift 3561124
  have htrace : WordTrace (prefixWord ++ tailWord_3561124) baseStart_3561124 baseEnd_3561124 := by
    simpa [prefixWord, tailWord_3561124, baseEnd_3561124] using wordTrace_append hprefix tailTrace_3561124
  have hstable : (prefixWord ++ tailWord_3561124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561124).length < 2 ^ (prefixWord ++ tailWord_3561124).sum := by decide
  have hdescent : baseEnd_3561124 < baseStart_3561124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561164 : List Nat := [2, 2, 1, 5, 2, 2, 1, 1, 7]
def baseStart_3561164 : Nat := 118140960795 + 3561164 * 2 ^ 59
def prefixEnd_3561164 : Nat := 4983230072969 + 3 ^ 40 * 3561164 * 2
def baseEnd_3561164 : Nat := 203176535720890018130279

theorem tailTrace_3561164 : CollatzResearch.WordTrace tailWord_3561164 prefixEnd_3561164 203176535720890018130279 := by
  unfold tailWord_3561164
  simp only [CollatzResearch.WordTrace]
  refine ⟨64943160835259250617581273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86590881113679000823441697 64943160835259250617581273)
  ·
    refine ⟨48707370626444437963185955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64943160835259250617581273 48707370626444437963185955)
    ·
      refine ⟨73061055939666656944778933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48707370626444437963185955 73061055939666656944778933)
      ·
        refine ⟨6849473994343749088573025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73061055939666656944778933 6849473994343749088573025)
        ·
          refine ⟨5137105495757811816429769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6849473994343749088573025 5137105495757811816429769)
          ·
            refine ⟨3852829121818358862322327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5137105495757811816429769 3852829121818358862322327)
            ·
              refine ⟨5779243682727538293483491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3852829121818358862322327 5779243682727538293483491)
              ·
                refine ⟨8668865524091307440225237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5779243682727538293483491 8668865524091307440225237)
                ·
                  refine ⟨203176535720890018130279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8668865524091307440225237 203176535720890018130279)
                  ·
                    rfl

theorem cell23_3561164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 1, 7].length) (baseStart_3561164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3561164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3561164 prefixEnd_3561164 := by exact prefixLift 3561164
  have htrace : WordTrace (prefixWord ++ tailWord_3561164) baseStart_3561164 baseEnd_3561164 := by
    simpa [prefixWord, tailWord_3561164, baseEnd_3561164] using wordTrace_append hprefix tailTrace_3561164
  have hstable : (prefixWord ++ tailWord_3561164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561164).length < 2 ^ (prefixWord ++ tailWord_3561164).sum := by decide
  have hdescent : baseEnd_3561164 < baseStart_3561164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561210 : List Nat := [3, 1, 1, 1, 1, 3, 1, 3, 2, 1, 6]
def baseStart_3561210 : Nat := 118140960795 + 3561210 * 2 ^ 59
def prefixEnd_3561210 : Nat := 4983230072969 + 3 ^ 40 * 3561210 * 2
def baseEnd_3561210 : Nat := 1828612441598116983197299

theorem tailTrace_3561210 : CollatzResearch.WordTrace tailWord_3561210 prefixEnd_3561210 1828612441598116983197299 := by
  unfold tailWord_3561210
  simp only [CollatzResearch.WordTrace]
  refine ⟨32471999857087962772834271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86591999618901234060891389 32471999857087962772834271)
  ·
    refine ⟨48707999785631944159251407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32471999857087962772834271 48707999785631944159251407)
    ·
      refine ⟨73061999678447916238877111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48707999785631944159251407 73061999678447916238877111)
      ·
        refine ⟨109592999517671874358315667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73061999678447916238877111 109592999517671874358315667)
        ·
          refine ⟨164389499276507811537473501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109592999517671874358315667 164389499276507811537473501)
          ·
            refine ⟨61646062228690429326552563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164389499276507811537473501 61646062228690429326552563)
            ·
              refine ⟨92469093343035643989828845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61646062228690429326552563 92469093343035643989828845)
              ·
                refine ⟨34675910003638366496185817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92469093343035643989828845 34675910003638366496185817)
                ·
                  refine ⟨26006932502728774872139363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34675910003638366496185817 26006932502728774872139363)
                  ·
                    refine ⟨39010398754093162308209045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26006932502728774872139363 39010398754093162308209045)
                    ·
                      refine ⟨1828612441598116983197299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39010398754093162308209045 1828612441598116983197299)
                      ·
                        rfl

theorem cell23_3561210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 2, 1, 6].length) (baseStart_3561210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3561210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3561210 prefixEnd_3561210 := by exact prefixLift 3561210
  have htrace : WordTrace (prefixWord ++ tailWord_3561210) baseStart_3561210 baseEnd_3561210 := by
    simpa [prefixWord, tailWord_3561210, baseEnd_3561210] using wordTrace_append hprefix tailTrace_3561210
  have hstable : (prefixWord ++ tailWord_3561210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561210).length < 2 ^ (prefixWord ++ tailWord_3561210).sum := by decide
  have hdescent : baseEnd_3561210 < baseStart_3561210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561237 : List Nat := [1, 3, 2, 1, 2, 3, 2, 3, 6]
def baseStart_3561237 : Nat := 118140960795 + 3561237 * 2 ^ 59
def prefixEnd_3561237 : Nat := 4983230072969 + 3 ^ 40 * 3561237 * 2
def baseEnd_3561237 : Nat := 203180700619532041951075

theorem tailTrace_3561237 : CollatzResearch.WordTrace tailWord_3561237 prefixEnd_3561237 203180700619532041951075 := by
  unfold tailWord_3561237
  simp only [CollatzResearch.WordTrace]
  refine ⟨129888984199254034702569965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86592656132836023135046643 129888984199254034702569965)
  ·
    refine ⟨48708369074720263013463737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129888984199254034702569965 48708369074720263013463737)
    ·
      refine ⟨36531276806040197260097803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48708369074720263013463737 36531276806040197260097803)
      ·
        refine ⟨54796915209060295890146705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36531276806040197260097803 54796915209060295890146705)
        ·
          refine ⟨41097686406795221917610029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54796915209060295890146705 41097686406795221917610029)
          ·
            refine ⟨15411632402548208219103761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41097686406795221917610029 15411632402548208219103761)
            ·
              refine ⟨11558724301911156164327821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15411632402548208219103761 11558724301911156164327821)
              ·
                refine ⟨4334521613216683561622933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11558724301911156164327821 4334521613216683561622933)
                ·
                  refine ⟨203180700619532041951075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4334521613216683561622933 203180700619532041951075)
                  ·
                    rfl

theorem cell23_3561237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 3, 6].length) (baseStart_3561237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3561237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3561237 prefixEnd_3561237 := by exact prefixLift 3561237
  have htrace : WordTrace (prefixWord ++ tailWord_3561237) baseStart_3561237 baseEnd_3561237 := by
    simpa [prefixWord, tailWord_3561237, baseEnd_3561237] using wordTrace_append hprefix tailTrace_3561237
  have hstable : (prefixWord ++ tailWord_3561237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561237).length < 2 ^ (prefixWord ++ tailWord_3561237).sum := by decide
  have hdescent : baseEnd_3561237 < baseStart_3561237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561280 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 2, 10]
def baseStart_3561280 : Nat := 118140960795 + 3561280 * 2 ^ 59
def prefixEnd_3561280 : Nat := 4983230072969 + 3 ^ 40 * 3561280 * 2
def baseEnd_3561280 : Nat := 609549461747977236440659

theorem tailTrace_3561280 : CollatzResearch.WordTrace tailWord_3561280 prefixEnd_3561280 609549461747977236440659 := by
  unfold tailWord_3561280
  simp only [CollatzResearch.WordTrace]
  refine ⟨64945276269049126523192647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86593701692065502030923529 64945276269049126523192647)
  ·
    refine ⟨97417914403573689784788971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64945276269049126523192647 97417914403573689784788971)
    ·
      refine ⟨146126871605360534677183457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97417914403573689784788971 146126871605360534677183457)
      ·
        refine ⟨109595153704020401007887593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146126871605360534677183457 109595153704020401007887593)
        ·
          refine ⟨82196365278015300755915695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109595153704020401007887593 82196365278015300755915695)
          ·
            refine ⟨123294547917022951133873543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82196365278015300755915695 123294547917022951133873543)
            ·
              refine ⟨184941821875534426700810315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123294547917022951133873543 184941821875534426700810315)
              ·
                refine ⟨277412732813301640051215473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184941821875534426700810315 277412732813301640051215473)
                ·
                  refine ⟨208059549609976230038411605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 277412732813301640051215473 208059549609976230038411605)
                  ·
                    refine ⟨609549461747977236440659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 208059549609976230038411605 609549461747977236440659)
                    ·
                      rfl

theorem cell23_3561280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 2, 10].length) (baseStart_3561280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3561280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3561280 prefixEnd_3561280 := by exact prefixLift 3561280
  have htrace : WordTrace (prefixWord ++ tailWord_3561280) baseStart_3561280 baseEnd_3561280 := by
    simpa [prefixWord, tailWord_3561280, baseEnd_3561280] using wordTrace_append hprefix tailTrace_3561280
  have hstable : (prefixWord ++ tailWord_3561280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561280).length < 2 ^ (prefixWord ++ tailWord_3561280).sum := by decide
  have hdescent : baseEnd_3561280 < baseStart_3561280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561287 : List Nat := [1, 1, 4, 1, 2, 1, 2, 1, 5, 1, 4]
def baseStart_3561287 : Nat := 118140960795 + 3561287 * 2 ^ 59
def prefixEnd_3561287 : Nat := 4983230072969 + 3 ^ 40 * 3561287 * 2
def baseEnd_3561287 : Nat := 1828651979608513181934445

theorem tailTrace_3561287 : CollatzResearch.WordTrace tailWord_3561287 prefixEnd_3561287 1828651979608513181934445 := by
  unfold tailWord_3561287
  simp only [CollatzResearch.WordTrace]
  refine ⟨129890807849072893241890115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86593871899381928827926743 129890807849072893241890115)
  ·
    refine ⟨194836211773609339862835173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129890807849072893241890115 194836211773609339862835173)
    ·
      refine ⟨36531789707551751224281595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194836211773609339862835173 36531789707551751224281595)
      ·
        refine ⟨54797684561327626836422393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36531789707551751224281595 54797684561327626836422393)
        ·
          refine ⟨41098263420995720127316795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54797684561327626836422393 41098263420995720127316795)
          ·
            refine ⟨61647395131493580190975193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41098263420995720127316795 61647395131493580190975193)
            ·
              refine ⟨46235546348620185143231395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61647395131493580190975193 46235546348620185143231395)
              ·
                refine ⟨69353319522930277714847093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46235546348620185143231395 69353319522930277714847093)
                ·
                  refine ⟨6501873705274713535766915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69353319522930277714847093 6501873705274713535766915)
                  ·
                    refine ⟨9752810557912070303650373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6501873705274713535766915 9752810557912070303650373)
                    ·
                      refine ⟨1828651979608513181934445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9752810557912070303650373 1828651979608513181934445)
                      ·
                        rfl

theorem cell23_3561287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 5, 1, 4].length) (baseStart_3561287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3561287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3561287 prefixEnd_3561287 := by exact prefixLift 3561287
  have htrace : WordTrace (prefixWord ++ tailWord_3561287) baseStart_3561287 baseEnd_3561287 := by
    simpa [prefixWord, tailWord_3561287, baseEnd_3561287] using wordTrace_append hprefix tailTrace_3561287
  have hstable : (prefixWord ++ tailWord_3561287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561287).length < 2 ^ (prefixWord ++ tailWord_3561287).sum := by decide
  have hdescent : baseEnd_3561287 < baseStart_3561287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561315 : List Nat := [1, 1, 1, 5, 4, 2, 1, 3, 1, 1, 3]
def baseStart_3561315 : Nat := 118140960795 + 3561315 * 2 ^ 59
def prefixEnd_3561315 : Nat := 4983230072969 + 3 ^ 40 * 3561315 * 2
def baseEnd_3561315 : Nat := 1828666357066839072384317

theorem tailTrace_3561315 : CollatzResearch.WordTrace tailWord_3561315 prefixEnd_3561315 1828666357066839072384317 := by
  unfold tailWord_3561315
  simp only [CollatzResearch.WordTrace]
  refine ⟨129891829092971454023909399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86594552728647636015939599 129891829092971454023909399)
  ·
    refine ⟨194837743639457181035864099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129891829092971454023909399 194837743639457181035864099)
    ·
      refine ⟨292256615459185771553796149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194837743639457181035864099 292256615459185771553796149)
      ·
        refine ⟨27399057699298666083168389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 292256615459185771553796149 27399057699298666083168389)
        ·
          refine ⟨5137323318618499890594073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27399057699298666083168389 5137323318618499890594073)
          ·
            refine ⟨3852992488963874917945555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5137323318618499890594073 3852992488963874917945555)
            ·
              refine ⟨5779488733445812376918333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3852992488963874917945555 5779488733445812376918333)
              ·
                refine ⟨2167308275042179641344375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5779488733445812376918333 2167308275042179641344375)
                ·
                  refine ⟨3250962412563269462016563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2167308275042179641344375 3250962412563269462016563)
                  ·
                    refine ⟨4876443618844904193024845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3250962412563269462016563 4876443618844904193024845)
                    ·
                      refine ⟨1828666357066839072384317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4876443618844904193024845 1828666357066839072384317)
                      ·
                        rfl

theorem cell23_3561315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 3, 1, 1, 3].length) (baseStart_3561315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3561315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3561315 prefixEnd_3561315 := by exact prefixLift 3561315
  have htrace : WordTrace (prefixWord ++ tailWord_3561315) baseStart_3561315 baseEnd_3561315 := by
    simpa [prefixWord, tailWord_3561315, baseEnd_3561315] using wordTrace_append hprefix tailTrace_3561315
  have hstable : (prefixWord ++ tailWord_3561315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561315).length < 2 ^ (prefixWord ++ tailWord_3561315).sum := by decide
  have hdescent : baseEnd_3561315 < baseStart_3561315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561317 : List Nat := [1, 3, 1, 3, 1, 1, 1, 3, 3, 2, 4]
def baseStart_3561317 : Nat := 118140960795 + 3561317 * 2 ^ 59
def prefixEnd_3561317 : Nat := 4983230072969 + 3 ^ 40 * 3561317 * 2
def baseEnd_3561317 : Nat := 1828667384028148064559307

theorem tailTrace_3561317 : CollatzResearch.WordTrace tailWord_3561317 prefixEnd_3561317 1828667384028148064559307 := by
  unfold tailWord_3561317
  simp only [CollatzResearch.WordTrace]
  refine ⟨129891902038964208365482205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86594601359309472243654803 129891902038964208365482205)
  ·
    refine ⟨48709463264611578137055827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129891902038964208365482205 48709463264611578137055827)
    ·
      refine ⟨73064194896917367205583741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48709463264611578137055827 73064194896917367205583741)
      ·
        refine ⟨27399073086344012702093903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73064194896917367205583741 27399073086344012702093903)
        ·
          refine ⟨41098609629516019053140855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27399073086344012702093903 41098609629516019053140855)
          ·
            refine ⟨61647914444274028579711283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41098609629516019053140855 61647914444274028579711283)
            ·
              refine ⟨92471871666411042869566925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61647914444274028579711283 92471871666411042869566925)
              ·
                refine ⟨34676951874904141076087597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92471871666411042869566925 34676951874904141076087597)
                ·
                  refine ⟨13003856953089052903532849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34676951874904141076087597 13003856953089052903532849)
                  ·
                    refine ⟨9752892714816789677649637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13003856953089052903532849 9752892714816789677649637)
                    ·
                      refine ⟨1828667384028148064559307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9752892714816789677649637 1828667384028148064559307)
                      ·
                        rfl

theorem cell23_3561317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_3561317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3561317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3561317 prefixEnd_3561317 := by exact prefixLift 3561317
  have htrace : WordTrace (prefixWord ++ tailWord_3561317) baseStart_3561317 baseEnd_3561317 := by
    simpa [prefixWord, tailWord_3561317, baseEnd_3561317] using wordTrace_append hprefix tailTrace_3561317
  have hstable : (prefixWord ++ tailWord_3561317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561317).length < 2 ^ (prefixWord ++ tailWord_3561317).sum := by decide
  have hdescent : baseEnd_3561317 < baseStart_3561317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561324 : List Nat := [2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 5]
def baseStart_3561324 : Nat := 118140960795 + 3561324 * 2 ^ 59
def prefixEnd_3561324 : Nat := 4983230072969 + 3 ^ 40 * 3561324 * 2
def baseEnd_3561324 : Nat := 1828670978392729537171775

theorem tailTrace_3561324 : CollatzResearch.WordTrace tailWord_3561324 prefixEnd_3561324 1828670978392729537171775 := by
  unfold tailWord_3561324
  simp only [CollatzResearch.WordTrace]
  refine ⟨64946078674969424280493513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86594771566625899040658017 64946078674969424280493513)
  ·
    refine ⟨48709559006227068210370135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64946078674969424280493513 48709559006227068210370135)
    ·
      refine ⟨73064338509340602315555203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48709559006227068210370135 73064338509340602315555203)
      ·
        refine ⟨109596507764010903473332805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73064338509340602315555203 109596507764010903473332805)
        ·
          refine ⟨20549345205752044401249901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109596507764010903473332805 20549345205752044401249901)
          ·
            refine ⟨7706004452157016650468713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20549345205752044401249901 7706004452157016650468713)
            ·
              refine ⟨5779503339117762487851535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7706004452157016650468713 5779503339117762487851535)
              ·
                refine ⟨8669255008676643731777303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5779503339117762487851535 8669255008676643731777303)
                ·
                  refine ⟨13003882513014965597665955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8669255008676643731777303 13003882513014965597665955)
                  ·
                    refine ⟨19505823769522448396498933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13003882513014965597665955 19505823769522448396498933)
                    ·
                      refine ⟨1828670978392729537171775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19505823769522448396498933 1828670978392729537171775)
                      ·
                        rfl

theorem cell23_3561324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 5].length) (baseStart_3561324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3561324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3561324 prefixEnd_3561324 := by exact prefixLift 3561324
  have htrace : WordTrace (prefixWord ++ tailWord_3561324) baseStart_3561324 baseEnd_3561324 := by
    simpa [prefixWord, tailWord_3561324, baseEnd_3561324] using wordTrace_append hprefix tailTrace_3561324
  have hstable : (prefixWord ++ tailWord_3561324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561324).length < 2 ^ (prefixWord ++ tailWord_3561324).sum := by decide
  have hdescent : baseEnd_3561324 < baseStart_3561324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561338 : List Nat := [3, 1, 1, 1, 1, 1, 4, 6, 1, 2, 2]
def baseStart_3561338 : Nat := 118140960795 + 3561338 * 2 ^ 59
def prefixEnd_3561338 : Nat := 4983230072969 + 3 ^ 40 * 3561338 * 2
def baseEnd_3561338 : Nat := 1828678167121892482396711

theorem tailTrace_3561338 : CollatzResearch.WordTrace tailWord_3561338 prefixEnd_3561338 1828678167121892482396711 := by
  unfold tailWord_3561338
  simp only [CollatzResearch.WordTrace]
  refine ⟨32473166992972032237999167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86595111981258752634664445 32473166992972032237999167)
  ·
    refine ⟨48709750489458048356998751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32473166992972032237999167 48709750489458048356998751)
    ·
      refine ⟨73064625734187072535498127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48709750489458048356998751 73064625734187072535498127)
      ·
        refine ⟨109596938601280608803247191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73064625734187072535498127 109596938601280608803247191)
        ·
          refine ⟨164395407901920913204870787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109596938601280608803247191 164395407901920913204870787)
          ·
            refine ⟨246593111852881369807306181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164395407901920913204870787 246593111852881369807306181)
            ·
              refine ⟨46236208472415256838869909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 246593111852881369807306181 46236208472415256838869909)
              ·
                refine ⟨2167322272144465164322027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46236208472415256838869909 2167322272144465164322027)
                ·
                  refine ⟨3250983408216697746483041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2167322272144465164322027 3250983408216697746483041)
                  ·
                    refine ⟨2438237556162523309862281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3250983408216697746483041 2438237556162523309862281)
                    ·
                      refine ⟨1828678167121892482396711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2438237556162523309862281 1828678167121892482396711)
                      ·
                        rfl

theorem cell23_3561338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 6, 1, 2, 2].length) (baseStart_3561338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3561338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3561338 prefixEnd_3561338 := by exact prefixLift 3561338
  have htrace : WordTrace (prefixWord ++ tailWord_3561338) baseStart_3561338 baseEnd_3561338 := by
    simpa [prefixWord, tailWord_3561338, baseEnd_3561338] using wordTrace_append hprefix tailTrace_3561338
  have hstable : (prefixWord ++ tailWord_3561338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561338).length < 2 ^ (prefixWord ++ tailWord_3561338).sum := by decide
  have hdescent : baseEnd_3561338 < baseStart_3561338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561358 : List Nat := [4, 1, 1, 5, 1, 1, 1, 1, 3, 2, 3]
def baseStart_3561358 : Nat := 118140960795 + 3561358 * 2 ^ 59
def prefixEnd_3561358 : Nat := 4983230072969 + 3 ^ 40 * 3561358 * 2
def baseEnd_3561358 : Nat := 1828688436734982404146619

theorem tailTrace_3561358 : CollatzResearch.WordTrace tailWord_3561358 prefixEnd_3561358 1828688436734982404146619 := by
  unfold tailWord_3561358
  simp only [CollatzResearch.WordTrace]
  refine ⟨16236674678976959045965591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86595598287877114911816485 16236674678976959045965591)
  ·
    refine ⟨24355012018465438568948387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16236674678976959045965591 24355012018465438568948387)
    ·
      refine ⟨36532518027698157853422581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24355012018465438568948387 36532518027698157853422581)
      ·
        refine ⟨3424923565096702298758367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36532518027698157853422581 3424923565096702298758367)
        ·
          refine ⟨5137385347645053448137551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3424923565096702298758367 5137385347645053448137551)
          ·
            refine ⟨7706078021467580172206327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5137385347645053448137551 7706078021467580172206327)
            ·
              refine ⟨11559117032201370258309491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7706078021467580172206327 11559117032201370258309491)
              ·
                refine ⟨17338675548302055387464237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11559117032201370258309491 17338675548302055387464237)
                ·
                  refine ⟨6502003330613270770299089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17338675548302055387464237 6502003330613270770299089)
                  ·
                    refine ⟨4876502497959953077724317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6502003330613270770299089 4876502497959953077724317)
                    ·
                      refine ⟨1828688436734982404146619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4876502497959953077724317 1828688436734982404146619)
                      ·
                        rfl

theorem cell23_3561358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_3561358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3561358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3561358 prefixEnd_3561358 := by exact prefixLift 3561358
  have htrace : WordTrace (prefixWord ++ tailWord_3561358) baseStart_3561358 baseEnd_3561358 := by
    simpa [prefixWord, tailWord_3561358, baseEnd_3561358] using wordTrace_append hprefix tailTrace_3561358
  have hstable : (prefixWord ++ tailWord_3561358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561358).length < 2 ^ (prefixWord ++ tailWord_3561358).sum := by decide
  have hdescent : baseEnd_3561358 < baseStart_3561358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561381 : List Nat := [1, 3, 1, 2, 1, 1, 1, 7, 1, 3, 2]
def baseStart_3561381 : Nat := 118140960795 + 3561381 * 2 ^ 59
def prefixEnd_3561381 : Nat := 4983230072969 + 3 ^ 40 * 3561381 * 2
def baseEnd_3561381 : Nat := 1828700246790035814159013

theorem tailTrace_3561381 : CollatzResearch.WordTrace tailWord_3561381 prefixEnd_3561381 1828700246790035814159013 := by
  unfold tailWord_3561381
  simp only [CollatzResearch.WordTrace]
  refine ⟨129894236310732347295811997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86596157540488231530541331 129894236310732347295811997)
  ·
    refine ⟨48710338616524630235929499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129894236310732347295811997 48710338616524630235929499)
    ·
      refine ⟨73065507924786945353894249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48710338616524630235929499 73065507924786945353894249)
      ·
        refine ⟨54799130943590209015420687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73065507924786945353894249 54799130943590209015420687)
        ·
          refine ⟨82198696415385313523131031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54799130943590209015420687 82198696415385313523131031)
          ·
            refine ⟨123298044623077970284696547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82198696415385313523131031 123298044623077970284696547)
            ·
              refine ⟨184947066934616955427044821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123298044623077970284696547 184947066934616955427044821)
              ·
                refine ⟨4334696881280084892821363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 184947066934616955427044821 4334696881280084892821363)
                ·
                  refine ⟨6502045321920127339232045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4334696881280084892821363 6502045321920127339232045)
                  ·
                    refine ⟨2438266995720047752212017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6502045321920127339232045 2438266995720047752212017)
                    ·
                      refine ⟨1828700246790035814159013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2438266995720047752212017 1828700246790035814159013)
                      ·
                        rfl

theorem cell23_3561381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 7, 1, 3, 2].length) (baseStart_3561381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3561381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3561381 prefixEnd_3561381 := by exact prefixLift 3561381
  have htrace : WordTrace (prefixWord ++ tailWord_3561381) baseStart_3561381 baseEnd_3561381 := by
    simpa [prefixWord, tailWord_3561381, baseEnd_3561381] using wordTrace_append hprefix tailTrace_3561381
  have hstable : (prefixWord ++ tailWord_3561381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561381).length < 2 ^ (prefixWord ++ tailWord_3561381).sum := by decide
  have hdescent : baseEnd_3561381 < baseStart_3561381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561417 : List Nat := [1, 2, 1, 1, 2, 1, 2, 6, 7]
def baseStart_3561417 : Nat := 118140960795 + 3561417 * 2 ^ 59
def prefixEnd_3561417 : Nat := 4983230072969 + 3 ^ 40 * 3561417 * 2
def baseEnd_3561417 : Nat := 203190970232621963700983

theorem tailTrace_3561417 : CollatzResearch.WordTrace tailWord_3561417 prefixEnd_3561417 203190970232621963700983 := by
  unfold tailWord_3561417
  simp only [CollatzResearch.WordTrace]
  refine ⟨129895549338601925444122505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86597032892401283629415003 129895549338601925444122505)
  ·
    refine ⟨97421662003951444083091879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129895549338601925444122505 97421662003951444083091879)
    ·
      refine ⟨146132493005927166124637819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97421662003951444083091879 146132493005927166124637819)
      ·
        refine ⟨219198739508890749186956729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146132493005927166124637819 219198739508890749186956729)
        ·
          refine ⟨164399054631668061890217547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219198739508890749186956729 164399054631668061890217547)
          ·
            refine ⟨246598581947502092835326321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164399054631668061890217547 246598581947502092835326321)
            ·
              refine ⟨184948936460626569626494741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246598581947502092835326321 184948936460626569626494741)
              ·
                refine ⟨8669481396591870451241941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 184948936460626569626494741 8669481396591870451241941)
                ·
                  refine ⟨203190970232621963700983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8669481396591870451241941 203190970232621963700983)
                  ·
                    rfl

theorem cell23_3561417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6, 7].length) (baseStart_3561417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3561417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3561417 prefixEnd_3561417 := by exact prefixLift 3561417
  have htrace : WordTrace (prefixWord ++ tailWord_3561417) baseStart_3561417 baseEnd_3561417 := by
    simpa [prefixWord, tailWord_3561417, baseEnd_3561417] using wordTrace_append hprefix tailTrace_3561417
  have hstable : (prefixWord ++ tailWord_3561417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561417).length < 2 ^ (prefixWord ++ tailWord_3561417).sum := by decide
  have hdescent : baseEnd_3561417 < baseStart_3561417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561428 : List Nat := [2, 4, 1, 2, 1, 1, 2, 2, 4, 2, 2]
def baseStart_3561428 : Nat := 118140960795 + 3561428 * 2 ^ 59
def prefixEnd_3561428 : Nat := 4983230072969 + 3 ^ 40 * 3561428 * 2
def baseEnd_3561428 : Nat := 1828724380380797130271297

theorem tailTrace_3561428 : CollatzResearch.WordTrace tailWord_3561428 prefixEnd_3561428 1828724380380797130271297 := by
  unfold tailWord_3561428
  simp only [CollatzResearch.WordTrace]
  refine ⟨64947975270781037161386469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86597300361041382881848625 64947975270781037161386469)
  ·
    refine ⟨12177745363271444467759963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64947975270781037161386469 12177745363271444467759963)
    ·
      refine ⟨18266618044907166701639945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12177745363271444467759963 18266618044907166701639945)
      ·
        refine ⟨13699963533680375026229959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18266618044907166701639945 13699963533680375026229959)
        ·
          refine ⟨20549945300520562539344939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13699963533680375026229959 20549945300520562539344939)
          ·
            refine ⟨30824917950780843809017409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20549945300520562539344939 30824917950780843809017409)
            ·
              refine ⟨23118688463085632856763057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30824917950780843809017409 23118688463085632856763057)
              ·
                refine ⟨17339016347314224642572293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23118688463085632856763057 17339016347314224642572293)
                ·
                  refine ⟨3251065565121417120482305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17339016347314224642572293 3251065565121417120482305)
                  ·
                    refine ⟨2438299173841062840361729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3251065565121417120482305 2438299173841062840361729)
                    ·
                      refine ⟨1828724380380797130271297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2438299173841062840361729 1828724380380797130271297)
                      ·
                        rfl

theorem cell23_3561428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_3561428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3561428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3561428 prefixEnd_3561428 := by exact prefixLift 3561428
  have htrace : WordTrace (prefixWord ++ tailWord_3561428) baseStart_3561428 baseEnd_3561428 := by
    simpa [prefixWord, tailWord_3561428, baseEnd_3561428] using wordTrace_append hprefix tailTrace_3561428
  have hstable : (prefixWord ++ tailWord_3561428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561428).length < 2 ^ (prefixWord ++ tailWord_3561428).sum := by decide
  have hdescent : baseEnd_3561428 < baseStart_3561428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561444 : List Nat := [2, 3, 1, 1, 1, 1, 3, 1, 4, 3, 3]
def baseStart_3561444 : Nat := 118140960795 + 3561444 * 2 ^ 59
def prefixEnd_3561444 : Nat := 4983230072969 + 3 ^ 40 * 3561444 * 2
def baseEnd_3561444 : Nat := 1828732596071269067671223

theorem tailTrace_3561444 : CollatzResearch.WordTrace tailWord_3561444 prefixEnd_3561444 1828732596071269067671223 := by
  unfold tailWord_3561444
  simp only [CollatzResearch.WordTrace]
  refine ⟨64948267054752054527677693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86597689406336072703570257 64948267054752054527677693)
  ·
    refine ⟨24355600145532020447879135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64948267054752054527677693 24355600145532020447879135)
    ·
      refine ⟨36533400218298030671818703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24355600145532020447879135 36533400218298030671818703)
      ·
        refine ⟨54800100327447046007728055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36533400218298030671818703 54800100327447046007728055)
        ·
          refine ⟨82200150491170569011592083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54800100327447046007728055 82200150491170569011592083)
          ·
            refine ⟨123300225736755853517388125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82200150491170569011592083 123300225736755853517388125)
            ·
              refine ⟨46237584651283445069020547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123300225736755853517388125 46237584651283445069020547)
              ·
                refine ⟨69356376976925167603530821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46237584651283445069020547 69356376976925167603530821)
                ·
                  refine ⟨13004320683173468925662029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69356376976925167603530821 13004320683173468925662029)
                  ·
                    refine ⟨4876620256190050847123261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13004320683173468925662029 4876620256190050847123261)
                    ·
                      refine ⟨1828732596071269067671223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4876620256190050847123261 1828732596071269067671223)
                      ·
                        rfl

theorem cell23_3561444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 4, 3, 3].length) (baseStart_3561444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3561444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3561444 prefixEnd_3561444 := by exact prefixLift 3561444
  have htrace : WordTrace (prefixWord ++ tailWord_3561444) baseStart_3561444 baseEnd_3561444 := by
    simpa [prefixWord, tailWord_3561444, baseEnd_3561444] using wordTrace_append hprefix tailTrace_3561444
  have hstable : (prefixWord ++ tailWord_3561444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561444).length < 2 ^ (prefixWord ++ tailWord_3561444).sum := by decide
  have hdescent : baseEnd_3561444 < baseStart_3561444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561462 : List Nat := [5, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2]
def baseStart_3561462 : Nat := 118140960795 + 3561462 * 2 ^ 59
def prefixEnd_3561462 : Nat := 4983230072969 + 3 ^ 40 * 3561462 * 2
def baseEnd_3561462 : Nat := 1828741838723049997246141

theorem tailTrace_3561462 : CollatzResearch.WordTrace tailWord_3561462 prefixEnd_3561462 1828741838723049997246141 := by
  unfold tailWord_3561462
  simp only [CollatzResearch.WordTrace]
  refine ⟨8118574413964931133094415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86598127082292598753007093 8118574413964931133094415)
  ·
    refine ⟨12177861620947396699641623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8118574413964931133094415 12177861620947396699641623)
    ·
      refine ⟨18266792431421095049462435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12177861620947396699641623 18266792431421095049462435)
      ·
        refine ⟨27400188647131642574193653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18266792431421095049462435 27400188647131642574193653)
        ·
          refine ⟨2568767685668591491330655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27400188647131642574193653 2568767685668591491330655)
          ·
            refine ⟨3853151528502887236995983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2568767685668591491330655 3853151528502887236995983)
            ·
              refine ⟨5779727292754330855493975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3853151528502887236995983 5779727292754330855493975)
              ·
                refine ⟨8669590939131496283240963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5779727292754330855493975 8669590939131496283240963)
                ·
                  refine ⟨13004386408697244424861445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8669590939131496283240963 13004386408697244424861445)
                  ·
                    refine ⟨2438322451630733329661521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13004386408697244424861445 2438322451630733329661521)
                    ·
                      refine ⟨1828741838723049997246141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2438322451630733329661521 1828741838723049997246141)
                      ·
                        rfl

theorem cell23_3561462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2].length) (baseStart_3561462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3561462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3561462 prefixEnd_3561462 := by exact prefixLift 3561462
  have htrace : WordTrace (prefixWord ++ tailWord_3561462) baseStart_3561462 baseEnd_3561462 := by
    simpa [prefixWord, tailWord_3561462, baseEnd_3561462] using wordTrace_append hprefix tailTrace_3561462
  have hstable : (prefixWord ++ tailWord_3561462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561462).length < 2 ^ (prefixWord ++ tailWord_3561462).sum := by decide
  have hdescent : baseEnd_3561462 < baseStart_3561462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561484 : List Nat := [2, 2, 1, 2, 3, 1, 1, 3, 1, 3, 4]
def baseStart_3561484 : Nat := 118140960795 + 3561484 * 2 ^ 59
def prefixEnd_3561484 : Nat := 4983230072969 + 3 ^ 40 * 3561484 * 2
def baseEnd_3561484 : Nat := 1828753135297448911171039

theorem tailTrace_3561484 : CollatzResearch.WordTrace tailWord_3561484 prefixEnd_3561484 1828753135297448911171039 := by
  unfold tailWord_3561484
  simp only [CollatzResearch.WordTrace]
  refine ⟨64948996514679597943405753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86598662019572797257874337 64948996514679597943405753)
  ·
    refine ⟨48711747386009698457554315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64948996514679597943405753 48711747386009698457554315)
    ·
      refine ⟨73067621079014547686331473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48711747386009698457554315 73067621079014547686331473)
      ·
        refine ⟨54800715809260910764748605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73067621079014547686331473 54800715809260910764748605)
        ·
          refine ⟨20550268428472841536780727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54800715809260910764748605 20550268428472841536780727)
          ·
            refine ⟨30825402642709262305171091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20550268428472841536780727 30825402642709262305171091)
            ·
              refine ⟨46238103964063893457756637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30825402642709262305171091 46238103964063893457756637)
              ·
                refine ⟨17339288986523960046658739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46238103964063893457756637 17339288986523960046658739)
                ·
                  refine ⟨26008933479785940069988109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17339288986523960046658739 26008933479785940069988109)
                  ·
                    refine ⟨9753350054919727526245541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26008933479785940069988109 9753350054919727526245541)
                    ·
                      refine ⟨1828753135297448911171039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9753350054919727526245541 1828753135297448911171039)
                      ·
                        rfl

theorem cell23_3561484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_3561484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3561484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3561484 prefixEnd_3561484 := by exact prefixLift 3561484
  have htrace : WordTrace (prefixWord ++ tailWord_3561484) baseStart_3561484 baseEnd_3561484 := by
    simpa [prefixWord, tailWord_3561484, baseEnd_3561484] using wordTrace_append hprefix tailTrace_3561484
  have hstable : (prefixWord ++ tailWord_3561484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561484).length < 2 ^ (prefixWord ++ tailWord_3561484).sum := by decide
  have hdescent : baseEnd_3561484 < baseStart_3561484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561487 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 11]
def baseStart_3561487 : Nat := 118140960795 + 3561487 * 2 ^ 59
def prefixEnd_3561487 : Nat := 4983230072969 + 3 ^ 40 * 3561487 * 2
def baseEnd_3561487 : Nat := 1828754675739412399433525

theorem tailTrace_3561487 : CollatzResearch.WordTrace tailWord_3561487 prefixEnd_3561487 1828754675739412399433525 := by
  unfold tailWord_3561487
  simp only [CollatzResearch.WordTrace]
  refine ⟨129898102448348327399170715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86598734965565551599447143 129898102448348327399170715)
  ·
    refine ⟨194847153672522491098756073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129898102448348327399170715 194847153672522491098756073)
    ·
      refine ⟨146135365254391868324067055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194847153672522491098756073 146135365254391868324067055)
      ·
        refine ⟨219203047881587802486100583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146135365254391868324067055 219203047881587802486100583)
        ·
          refine ⟨328804571822381703729150875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219203047881587802486100583 328804571822381703729150875)
          ·
            refine ⟨493206857733572555593726313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328804571822381703729150875 493206857733572555593726313)
            ·
              refine ⟨369905143300179416695294735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 493206857733572555593726313 369905143300179416695294735)
              ·
                refine ⟨554857714950269125042942103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 369905143300179416695294735 554857714950269125042942103)
                ·
                  refine ⟨832286572425403687564413155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 554857714950269125042942103 832286572425403687564413155)
                  ·
                    refine ⟨1248429858638105531346619733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 832286572425403687564413155 1248429858638105531346619733)
                    ·
                      refine ⟨1828754675739412399433525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 1248429858638105531346619733 1828754675739412399433525)
                      ·
                        rfl

theorem cell23_3561487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 11].length) (baseStart_3561487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3561487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3561487 prefixEnd_3561487 := by exact prefixLift 3561487
  have htrace : WordTrace (prefixWord ++ tailWord_3561487) baseStart_3561487 baseEnd_3561487 := by
    simpa [prefixWord, tailWord_3561487, baseEnd_3561487] using wordTrace_append hprefix tailTrace_3561487
  have hstable : (prefixWord ++ tailWord_3561487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561487).length < 2 ^ (prefixWord ++ tailWord_3561487).sum := by decide
  have hdescent : baseEnd_3561487 < baseStart_3561487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561501 : List Nat := [1, 4, 2, 2, 2, 1, 1, 1, 4, 1, 4]
def baseStart_3561501 : Nat := 118140960795 + 3561501 * 2 ^ 59
def prefixEnd_3561501 : Nat := 4983230072969 + 3 ^ 40 * 3561501 * 2
def baseEnd_3561501 : Nat := 1828761864468575344658461

theorem tailTrace_3561501 : CollatzResearch.WordTrace tailWord_3561501 prefixEnd_3561501 1828761864468575344658461 := by
  unfold tailWord_3561501
  simp only [CollatzResearch.WordTrace]
  refine ⟨129898613070297607790180357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86599075380198405193453571 129898613070297607790180357)
  ·
    refine ⟨24355989950680801460658817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129898613070297607790180357 24355989950680801460658817)
    ·
      refine ⟨18266992463010601095494113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24355989950680801460658817 18266992463010601095494113)
      ·
        refine ⟨13700244347257950821620585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18266992463010601095494113 13700244347257950821620585)
        ·
          refine ⟨10275183260443463116215439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13700244347257950821620585 10275183260443463116215439)
          ·
            refine ⟨15412774890665194674323159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10275183260443463116215439 15412774890665194674323159)
            ·
              refine ⟨23119162335997792011484739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15412774890665194674323159 23119162335997792011484739)
              ·
                refine ⟨34678743503996688017227109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23119162335997792011484739 34678743503996688017227109)
                ·
                  refine ⟨6502264406999379003230083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34678743503996688017227109 6502264406999379003230083)
                  ·
                    refine ⟨9753396610499068504845125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6502264406999379003230083 9753396610499068504845125)
                    ·
                      refine ⟨1828761864468575344658461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9753396610499068504845125 1828761864468575344658461)
                      ·
                        rfl

theorem cell23_3561501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_3561501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3561501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3561501 prefixEnd_3561501 := by exact prefixLift 3561501
  have htrace : WordTrace (prefixWord ++ tailWord_3561501) baseStart_3561501 baseEnd_3561501 := by
    simpa [prefixWord, tailWord_3561501, baseEnd_3561501] using wordTrace_append hprefix tailTrace_3561501
  have hstable : (prefixWord ++ tailWord_3561501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561501).length < 2 ^ (prefixWord ++ tailWord_3561501).sum := by decide
  have hdescent : baseEnd_3561501 < baseStart_3561501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561551 : List Nat := [1, 1, 2, 1, 1, 2, 2, 4, 5, 1, 3]
def baseStart_3561551 : Nat := 118140960795 + 3561551 * 2 ^ 59
def prefixEnd_3561551 : Nat := 4983230072969 + 3 ^ 40 * 3561551 * 2
def baseEnd_3561551 : Nat := 1828787538501300149033231

theorem tailTrace_3561551 : CollatzResearch.WordTrace tailWord_3561551 prefixEnd_3561551 1828787538501300149033231 := by
  unfold tailWord_3561551
  simp only [CollatzResearch.WordTrace]
  refine ⟨129900436720116466329500507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86600291146744310886333671 129900436720116466329500507)
  ·
    refine ⟨194850655080174699494250761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129900436720116466329500507 194850655080174699494250761)
    ·
      refine ⟨146137991310131024620688071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194850655080174699494250761 146137991310131024620688071)
      ·
        refine ⟨219206986965196536931032107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146137991310131024620688071 219206986965196536931032107)
        ·
          refine ⟨328810480447794805396548161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219206986965196536931032107 328810480447794805396548161)
          ·
            refine ⟨246607860335846104047411121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 328810480447794805396548161 246607860335846104047411121)
            ·
              refine ⟨184955895251884578035558341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246607860335846104047411121 184955895251884578035558341)
              ·
                refine ⟨34679230359728358381667189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 184955895251884578035558341 34679230359728358381667189)
                ·
                  refine ⟨3251177846224533598281299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34679230359728358381667189 3251177846224533598281299)
                  ·
                    refine ⟨4876766769336800397421949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3251177846224533598281299 4876766769336800397421949)
                    ·
                      refine ⟨1828787538501300149033231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4876766769336800397421949 1828787538501300149033231)
                      ·
                        rfl

theorem cell23_3561551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 5, 1, 3].length) (baseStart_3561551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3561551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3561551 prefixEnd_3561551 := by exact prefixLift 3561551
  have htrace : WordTrace (prefixWord ++ tailWord_3561551) baseStart_3561551 baseEnd_3561551 := by
    simpa [prefixWord, tailWord_3561551, baseEnd_3561551] using wordTrace_append hprefix tailTrace_3561551
  have hstable : (prefixWord ++ tailWord_3561551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561551).length < 2 ^ (prefixWord ++ tailWord_3561551).sum := by decide
  have hdescent : baseEnd_3561551 < baseStart_3561551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561591 : List Nat := [1, 1, 3, 1, 1, 5, 2, 1, 3, 1, 4]
def baseStart_3561591 : Nat := 118140960795 + 3561591 * 2 ^ 59
def prefixEnd_3561591 : Nat := 4983230072969 + 3 ^ 40 * 3561591 * 2
def baseEnd_3561591 : Nat := 1828808077727479992533047

theorem tailTrace_3561591 : CollatzResearch.WordTrace tailWord_3561591 prefixEnd_3561591 1828808077727479992533047 := by
  unfold tailWord_3561591
  simp only [CollatzResearch.WordTrace]
  refine ⟨129901895639971553160956627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86601263759981035440637751 129901895639971553160956627)
  ·
    refine ⟨194852843459957329741434941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129901895639971553160956627 194852843459957329741434941)
    ·
      refine ⟨73069816297483998653038103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194852843459957329741434941 73069816297483998653038103)
      ·
        refine ⟨109604724446225997979557155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73069816297483998653038103 109604724446225997979557155)
        ·
          refine ⟨164407086669338996969335733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109604724446225997979557155 164407086669338996969335733)
          ·
            refine ⟨15413164375250530965875225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 164407086669338996969335733 15413164375250530965875225)
            ·
              refine ⟨11559873281437898224406419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15413164375250530965875225 11559873281437898224406419)
              ·
                refine ⟨17339809922156847336609629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11559873281437898224406419 17339809922156847336609629)
                ·
                  refine ⟨6502428720808817751228611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17339809922156847336609629 6502428720808817751228611)
                  ·
                    refine ⟨9753643081213226626842917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6502428720808817751228611 9753643081213226626842917)
                    ·
                      refine ⟨1828808077727479992533047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9753643081213226626842917 1828808077727479992533047)
                      ·
                        rfl

theorem cell23_3561591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 3, 1, 4].length) (baseStart_3561591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3561591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3561591 prefixEnd_3561591 := by exact prefixLift 3561591
  have htrace : WordTrace (prefixWord ++ tailWord_3561591) baseStart_3561591 baseEnd_3561591 := by
    simpa [prefixWord, tailWord_3561591, baseEnd_3561591] using wordTrace_append hprefix tailTrace_3561591
  have hstable : (prefixWord ++ tailWord_3561591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561591).length < 2 ^ (prefixWord ++ tailWord_3561591).sum := by decide
  have hdescent : baseEnd_3561591 < baseStart_3561591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561605 : List Nat := [1, 3, 1, 1, 5, 3, 2, 1, 1, 5]
def baseStart_3561605 : Nat := 118140960795 + 3561605 * 2 ^ 59
def prefixEnd_3561605 : Nat := 4983230072969 + 3 ^ 40 * 3561605 * 2
def baseEnd_3561605 : Nat := 609605088818880979252661

theorem tailTrace_3561605 : CollatzResearch.WordTrace tailWord_3561605 prefixEnd_3561605 609605088818880979252661 := by
  unfold tailWord_3561605
  simp only [CollatzResearch.WordTrace]
  refine ⟨129902406261920833551966269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86601604174613889034644179 129902406261920833551966269)
  ·
    refine ⟨48713402348220312581987351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129902406261920833551966269 48713402348220312581987351)
    ·
      refine ⟨73070103522330468872981027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48713402348220312581987351 73070103522330468872981027)
      ·
        refine ⟨109605155283495703309471541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73070103522330468872981027 109605155283495703309471541)
        ·
          refine ⟨10275483307827722185262957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 109605155283495703309471541 10275483307827722185262957)
          ·
            refine ⟨3853306240435395819473609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10275483307827722185262957 3853306240435395819473609)
            ·
              refine ⟨2889979680326546864605207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3853306240435395819473609 2889979680326546864605207)
              ·
                refine ⟨4334969520489820296907811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2889979680326546864605207 4334969520489820296907811)
                ·
                  refine ⟨6502454280734730445361717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4334969520489820296907811 6502454280734730445361717)
                  ·
                    refine ⟨609605088818880979252661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6502454280734730445361717 609605088818880979252661)
                    ·
                      rfl

theorem cell23_3561605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 1, 1, 5].length) (baseStart_3561605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3561605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3561605 prefixEnd_3561605 := by exact prefixLift 3561605
  have htrace : WordTrace (prefixWord ++ tailWord_3561605) baseStart_3561605 baseEnd_3561605 := by
    simpa [prefixWord, tailWord_3561605, baseEnd_3561605] using wordTrace_append hprefix tailTrace_3561605
  have hstable : (prefixWord ++ tailWord_3561605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561605).length < 2 ^ (prefixWord ++ tailWord_3561605).sum := by decide
  have hdescent : baseEnd_3561605 < baseStart_3561605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561618 : List Nat := [3, 2, 3, 1, 1, 1, 3, 1, 4, 4]
def baseStart_3561618 : Nat := 118140960795 + 3561618 * 2 ^ 59
def prefixEnd_3561618 : Nat := 4983230072969 + 3 ^ 40 * 3561618 * 2
def baseEnd_3561618 : Nat := 609607313901717128965141

theorem tailTrace_3561618 : CollatzResearch.WordTrace tailWord_3561618 prefixEnd_3561618 609607313901717128965141 := by
  unfold tailWord_3561618
  simp only [CollatzResearch.WordTrace]
  refine ⟨32475720102718434193047377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86601920273915824514793005 32475720102718434193047377)
  ·
    refine ⟨24356790077038825644785533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32475720102718434193047377 24356790077038825644785533)
    ·
      refine ⟨9133796278889559616794575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24356790077038825644785533 9133796278889559616794575)
      ·
        refine ⟨13700694418334339425191863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9133796278889559616794575 13700694418334339425191863)
        ·
          refine ⟨20551041627501509137787795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13700694418334339425191863 20551041627501509137787795)
          ·
            refine ⟨30826562441252263706681693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20551041627501509137787795 30826562441252263706681693)
            ·
              refine ⟨11559960915469598890005635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30826562441252263706681693 11559960915469598890005635)
              ·
                refine ⟨17339941373204398335008453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11559960915469598890005635 17339941373204398335008453)
                ·
                  refine ⟨3251239007475824687814085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17339941373204398335008453 3251239007475824687814085)
                  ·
                    refine ⟨609607313901717128965141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3251239007475824687814085 609607313901717128965141)
                    ·
                      rfl

theorem cell23_3561618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_3561618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3561618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3561618 prefixEnd_3561618 := by exact prefixLift 3561618
  have htrace : WordTrace (prefixWord ++ tailWord_3561618) baseStart_3561618 baseEnd_3561618 := by
    simpa [prefixWord, tailWord_3561618, baseEnd_3561618] using wordTrace_append hprefix tailTrace_3561618
  have hstable : (prefixWord ++ tailWord_3561618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561618).length < 2 ^ (prefixWord ++ tailWord_3561618).sum := by decide
  have hdescent : baseEnd_3561618 < baseStart_3561618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561642 : List Nat := [3, 1, 5, 1, 2, 1, 2, 2, 1, 1, 4]
def baseStart_3561642 : Nat := 118140960795 + 3561642 * 2 ^ 59
def prefixEnd_3561642 : Nat := 4983230072969 + 3 ^ 40 * 3561642 * 2
def baseEnd_3561642 : Nat := 1828834265240859292995313

theorem tailTrace_3561642 : CollatzResearch.WordTrace tailWord_3561642 prefixEnd_3561642 1828834265240859292995313 := by
  unfold tailWord_3561642
  simp only [CollatzResearch.WordTrace]
  refine ⟨32475938940696697217765795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86602503841857859247375453 32475938940696697217765795)
  ·
    refine ⟨48713908411045045826648693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32475938940696697217765795 48713908411045045826648693)
    ·
      refine ⟨4566928913535473046248315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48713908411045045826648693 4566928913535473046248315)
      ·
        refine ⟨6850393370303209569372473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4566928913535473046248315 6850393370303209569372473)
        ·
          refine ⟨5137795027727407177029355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6850393370303209569372473 5137795027727407177029355)
          ·
            refine ⟨7706692541591110765544033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5137795027727407177029355 7706692541591110765544033)
            ·
              refine ⟨5780019406193333074158025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7706692541591110765544033 5780019406193333074158025)
              ·
                refine ⟨4335014554644999805618519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5780019406193333074158025 4335014554644999805618519)
                ·
                  refine ⟨6502521831967499708427779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4335014554644999805618519 6502521831967499708427779)
                  ·
                    refine ⟨9753782747951249562641669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6502521831967499708427779 9753782747951249562641669)
                    ·
                      refine ⟨1828834265240859292995313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9753782747951249562641669 1828834265240859292995313)
                      ·
                        rfl

theorem cell23_3561642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_3561642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3561642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3561642 prefixEnd_3561642 := by exact prefixLift 3561642
  have htrace : WordTrace (prefixWord ++ tailWord_3561642) baseStart_3561642 baseEnd_3561642 := by
    simpa [prefixWord, tailWord_3561642, baseEnd_3561642] using wordTrace_append hprefix tailTrace_3561642
  have hstable : (prefixWord ++ tailWord_3561642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561642).length < 2 ^ (prefixWord ++ tailWord_3561642).sum := by decide
  have hdescent : baseEnd_3561642 < baseStart_3561642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561644 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 3, 9]
def baseStart_3561644 : Nat := 118140960795 + 3561644 * 2 ^ 59
def prefixEnd_3561644 : Nat := 4983230072969 + 3 ^ 40 * 3561644 * 2
def baseEnd_3561644 : Nat := 609611764067389428390101

theorem tailTrace_3561644 : CollatzResearch.WordTrace tailWord_3561644 prefixEnd_3561644 609611764067389428390101 := by
  unfold tailWord_3561644
  simp only [CollatzResearch.WordTrace]
  refine ⟨64951914354389771606317993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86602552472519695475090657 64951914354389771606317993)
  ·
    refine ⟨48713935765792328704738495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64951914354389771606317993 48713935765792328704738495)
    ·
      refine ⟨73070903648688493057107743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48713935765792328704738495 73070903648688493057107743)
      ·
        refine ⟨109606355473032739585661615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73070903648688493057107743 109606355473032739585661615)
        ·
          refine ⟨164409533209549109378492423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109606355473032739585661615 164409533209549109378492423)
          ·
            refine ⟨246614299814323664067738635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164409533209549109378492423 246614299814323664067738635)
            ·
              refine ⟨369921449721485496101607953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246614299814323664067738635 369921449721485496101607953)
              ·
                refine ⟨277441087291114122076205965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 369921449721485496101607953 277441087291114122076205965)
                ·
                  refine ⟨104040407734167795778577237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 277441087291114122076205965 104040407734167795778577237)
                  ·
                    refine ⟨609611764067389428390101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 104040407734167795778577237 609611764067389428390101)
                    ·
                      rfl

theorem cell23_3561644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 9].length) (baseStart_3561644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3561644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3561644 prefixEnd_3561644 := by exact prefixLift 3561644
  have htrace : WordTrace (prefixWord ++ tailWord_3561644) baseStart_3561644 baseEnd_3561644 := by
    simpa [prefixWord, tailWord_3561644, baseEnd_3561644] using wordTrace_append hprefix tailTrace_3561644
  have hstable : (prefixWord ++ tailWord_3561644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561644).length < 2 ^ (prefixWord ++ tailWord_3561644).sum := by decide
  have hdescent : baseEnd_3561644 < baseStart_3561644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561645 : List Nat := [1, 5, 2, 1, 2, 1, 1, 4, 1, 2, 3]
def baseStart_3561645 : Nat := 118140960795 + 3561645 * 2 ^ 59
def prefixEnd_3561645 : Nat := 4983230072969 + 3 ^ 40 * 3561645 * 2
def baseEnd_3561645 : Nat := 1828835805682822781257799

theorem tailTrace_3561645 : CollatzResearch.WordTrace tailWord_3561645 prefixEnd_3561645 1828835805682822781257799 := by
  unfold tailWord_3561645
  simp only [CollatzResearch.WordTrace]
  refine ⟨129903865181775920383422389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86602576787850613588948259 129903865181775920383422389)
  ·
    refine ⟨12178487360791492535945849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 129903865181775920383422389 12178487360791492535945849)
    ·
      refine ⟨9133865520593619401959387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12178487360791492535945849 9133865520593619401959387)
      ·
        refine ⟨13700798280890429102939081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9133865520593619401959387 13700798280890429102939081)
        ·
          refine ⟨10275598710667821827204311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13700798280890429102939081 10275598710667821827204311)
          ·
            refine ⟨15413398066001732740806467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10275598710667821827204311 15413398066001732740806467)
            ·
              refine ⟨23120097099002599111209701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15413398066001732740806467 23120097099002599111209701)
              ·
                refine ⟨4335018206062987333351819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23120097099002599111209701 4335018206062987333351819)
                ·
                  refine ⟨6502527309094481000027729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4335018206062987333351819 6502527309094481000027729)
                  ·
                    refine ⟨4876895481820860750020797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6502527309094481000027729 4876895481820860750020797)
                    ·
                      refine ⟨1828835805682822781257799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4876895481820860750020797 1828835805682822781257799)
                      ·
                        rfl

theorem cell23_3561645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_3561645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3561645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3561645 prefixEnd_3561645 := by exact prefixLift 3561645
  have htrace : WordTrace (prefixWord ++ tailWord_3561645) baseStart_3561645 baseEnd_3561645 := by
    simpa [prefixWord, tailWord_3561645, baseEnd_3561645] using wordTrace_append hprefix tailTrace_3561645
  have hstable : (prefixWord ++ tailWord_3561645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561645).length < 2 ^ (prefixWord ++ tailWord_3561645).sum := by decide
  have hdescent : baseEnd_3561645 < baseStart_3561645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561658 : List Nat := [3, 1, 1, 1, 2, 2, 3, 2, 4, 1, 3]
def baseStart_3561658 : Nat := 118140960795 + 3561658 * 2 ^ 59
def prefixEnd_3561658 : Nat := 4983230072969 + 3 ^ 40 * 3561658 * 2
def baseEnd_3561658 : Nat := 1828842480931331230395239

theorem tailTrace_3561658 : CollatzResearch.WordTrace tailWord_3561658 prefixEnd_3561658 1828842480931331230395239 := by
  unfold tailWord_3561658
  simp only [CollatzResearch.WordTrace]
  refine ⟨32476084832682205900911407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86602892887152549069097085 32476084832682205900911407)
  ·
    refine ⟨48714127249023308851367111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32476084832682205900911407 48714127249023308851367111)
    ·
      refine ⟨73071190873534963277050667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48714127249023308851367111 73071190873534963277050667)
      ·
        refine ⟨109606786310302444915576001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73071190873534963277050667 109606786310302444915576001)
        ·
          refine ⟨82205089732726833686682001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109606786310302444915576001 82205089732726833686682001)
          ·
            refine ⟨61653817299545125265011501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82205089732726833686682001 61653817299545125265011501)
            ·
              refine ⟨23120181487329421974379313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61653817299545125265011501 23120181487329421974379313)
              ·
                refine ⟨17340136115497066480784485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23120181487329421974379313 17340136115497066480784485)
                ·
                  refine ⟨3251275521655699965147091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17340136115497066480784485 3251275521655699965147091)
                  ·
                    refine ⟨4876913282483549947720637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3251275521655699965147091 4876913282483549947720637)
                    ·
                      refine ⟨1828842480931331230395239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4876913282483549947720637 1828842480931331230395239)
                      ·
                        rfl

theorem cell23_3561658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 4, 1, 3].length) (baseStart_3561658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3561658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3561658 prefixEnd_3561658 := by exact prefixLift 3561658
  have htrace : WordTrace (prefixWord ++ tailWord_3561658) baseStart_3561658 baseEnd_3561658 := by
    simpa [prefixWord, tailWord_3561658, baseEnd_3561658] using wordTrace_append hprefix tailTrace_3561658
  have hstable : (prefixWord ++ tailWord_3561658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561658).length < 2 ^ (prefixWord ++ tailWord_3561658).sum := by decide
  have hdescent : baseEnd_3561658 < baseStart_3561658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561665 : List Nat := [1, 2, 6, 1, 3, 1, 9]
def baseStart_3561665 : Nat := 118140960795 + 3561665 * 2 ^ 59
def prefixEnd_3561665 : Nat := 4983230072969 + 3 ^ 40 * 3561665 * 2
def baseEnd_3561665 : Nat := 22578346608591514851947

theorem tailTrace_3561665 : CollatzResearch.WordTrace tailWord_3561665 prefixEnd_3561665 22578346608591514851947 := by
  unfold tailWord_3561665
  simp only [CollatzResearch.WordTrace]
  refine ⟨129904594641703463799150449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86603063094468975866100299 129904594641703463799150449)
  ·
    refine ⟨97428445981277597849362837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129904594641703463799150449 97428445981277597849362837)
    ·
      refine ⟨4566958405372387399188883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 97428445981277597849362837 4566958405372387399188883)
      ·
        refine ⟨6850437608058581098783325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4566958405372387399188883 6850437608058581098783325)
        ·
          refine ⟨2568914103021967912043747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6850437608058581098783325 2568914103021967912043747)
          ·
            refine ⟨3853371154532951868065621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2568914103021967912043747 3853371154532951868065621)
            ·
              refine ⟨22578346608591514851947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3853371154532951868065621 22578346608591514851947)
              ·
                rfl

theorem cell23_3561665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 9].length) (baseStart_3561665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3561665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3561665 prefixEnd_3561665 := by exact prefixLift 3561665
  have htrace : WordTrace (prefixWord ++ tailWord_3561665) baseStart_3561665 baseEnd_3561665 := by
    simpa [prefixWord, tailWord_3561665, baseEnd_3561665] using wordTrace_append hprefix tailTrace_3561665
  have hstable : (prefixWord ++ tailWord_3561665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561665).length < 2 ^ (prefixWord ++ tailWord_3561665).sum := by decide
  have hdescent : baseEnd_3561665 < baseStart_3561665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561676 : List Nat := [2, 2, 1, 6, 2, 1, 1, 1, 3, 2, 2]
def baseStart_3561676 : Nat := 118140960795 + 3561676 * 2 ^ 59
def prefixEnd_3561676 : Nat := 4983230072969 + 3 ^ 40 * 3561676 * 2
def baseEnd_3561676 : Nat := 1828851723583112159970157

theorem tailTrace_3561676 : CollatzResearch.WordTrace tailWord_3561676 prefixEnd_3561676 1828851723583112159970157 := by
  unfold tailWord_3561676
  simp only [CollatzResearch.WordTrace]
  refine ⟨64952497922331806338900441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86603330563109075118533921 64952497922331806338900441)
  ·
    refine ⟨48714373441748854754175331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64952497922331806338900441 48714373441748854754175331)
    ·
      refine ⟨73071560162623282131262997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48714373441748854754175331 73071560162623282131262997)
      ·
        refine ⟨3425229382622966349902953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 73071560162623282131262997 3425229382622966349902953)
        ·
          refine ⟨2568922036967224762427215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3425229382622966349902953 2568922036967224762427215)
          ·
            refine ⟨3853383055450837143640823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2568922036967224762427215 3853383055450837143640823)
            ·
              refine ⟨5780074583176255715461235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3853383055450837143640823 5780074583176255715461235)
              ·
                refine ⟨8670111874764383573191853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5780074583176255715461235 8670111874764383573191853)
                ·
                  refine ⟨3251291953036643839946945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8670111874764383573191853 3251291953036643839946945)
                  ·
                    refine ⟨2438468964777482879960209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3251291953036643839946945 2438468964777482879960209)
                    ·
                      refine ⟨1828851723583112159970157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2438468964777482879960209 1828851723583112159970157)
                      ·
                        rfl

theorem cell23_3561676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_3561676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3561676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3561676 prefixEnd_3561676 := by exact prefixLift 3561676
  have htrace : WordTrace (prefixWord ++ tailWord_3561676) baseStart_3561676 baseEnd_3561676 := by
    simpa [prefixWord, tailWord_3561676, baseEnd_3561676] using wordTrace_append hprefix tailTrace_3561676
  have hstable : (prefixWord ++ tailWord_3561676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561676).length < 2 ^ (prefixWord ++ tailWord_3561676).sum := by decide
  have hdescent : baseEnd_3561676 < baseStart_3561676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561718 : List Nat := [5, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5]
def baseStart_3561718 : Nat := 118140960795 + 3561718 * 2 ^ 59
def prefixEnd_3561718 : Nat := 4983230072969 + 3 ^ 40 * 3561718 * 2
def baseEnd_3561718 : Nat := 1828873289770600995644963

theorem tailTrace_3561718 : CollatzResearch.WordTrace tailWord_3561718 prefixEnd_3561718 1828873289770600995644963 := by
  unfold tailWord_3561718
  simp only [CollatzResearch.WordTrace]
  refine ⟨8119157981906965865676863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86604351807007635900553205 8119157981906965865676863)
  ·
    refine ⟨12178736972860448798515295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8119157981906965865676863 12178736972860448798515295)
    ·
      refine ⟨18268105459290673197772943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12178736972860448798515295 18268105459290673197772943)
      ·
        refine ⟨27402158188936009796659415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18268105459290673197772943 27402158188936009796659415)
        ·
          refine ⟨41103237283404014694989123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27402158188936009796659415 41103237283404014694989123)
          ·
            refine ⟨61654855925106022042483685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41103237283404014694989123 61654855925106022042483685)
            ·
              refine ⟨11560285485957379132965691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61654855925106022042483685 11560285485957379132965691)
              ·
                refine ⟨17340428228936068699448537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11560285485957379132965691 17340428228936068699448537)
                ·
                  refine ⟨13005321171702051524586403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17340428228936068699448537 13005321171702051524586403)
                  ·
                    refine ⟨19507981757553077286879605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13005321171702051524586403 19507981757553077286879605)
                    ·
                      refine ⟨1828873289770600995644963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19507981757553077286879605 1828873289770600995644963)
                      ·
                        rfl

theorem cell23_3561718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_3561718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3561718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3561718 prefixEnd_3561718 := by exact prefixLift 3561718
  have htrace : WordTrace (prefixWord ++ tailWord_3561718) baseStart_3561718 baseEnd_3561718 := by
    simpa [prefixWord, tailWord_3561718, baseEnd_3561718] using wordTrace_append hprefix tailTrace_3561718
  have hstable : (prefixWord ++ tailWord_3561718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561718).length < 2 ^ (prefixWord ++ tailWord_3561718).sum := by decide
  have hdescent : baseEnd_3561718 < baseStart_3561718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561761 : List Nat := [1, 2, 3, 2, 1, 1, 2, 2, 1, 1, 7]
def baseStart_3561761 : Nat := 118140960795 + 3561761 * 2 ^ 59
def prefixEnd_3561761 : Nat := 4983230072969 + 3 ^ 40 * 3561761 * 2
def baseEnd_3561761 : Nat := 1828895369438744327407265

theorem tailTrace_3561761 : CollatzResearch.WordTrace tailWord_3561761 prefixEnd_3561761 1828895369438744327407265 := by
  unfold tailWord_3561761
  simp only [CollatzResearch.WordTrace]
  refine ⟨129908096049355672194645137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86605397366237114796430091 129908096049355672194645137)
  ·
    refine ⟨97431072037016754145983853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129908096049355672194645137 97431072037016754145983853)
    ·
      refine ⟨36536652013881282804743945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97431072037016754145983853 36536652013881282804743945)
      ·
        refine ⟨27402489010410962103557959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36536652013881282804743945 27402489010410962103557959)
        ·
          refine ⟨41103733515616443155336939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27402489010410962103557959 41103733515616443155336939)
          ·
            refine ⟨61655600273424664733005409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41103733515616443155336939 61655600273424664733005409)
            ·
              refine ⟨46241700205068498549754057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61655600273424664733005409 46241700205068498549754057)
              ·
                refine ⟨34681275153801373912315543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46241700205068498549754057 34681275153801373912315543)
                ·
                  refine ⟨52021912730702060868473315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34681275153801373912315543 52021912730702060868473315)
                  ·
                    refine ⟨78032869096053091302709973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52021912730702060868473315 78032869096053091302709973)
                    ·
                      refine ⟨1828895369438744327407265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 78032869096053091302709973 1828895369438744327407265)
                      ·
                        rfl

theorem cell23_3561761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_3561761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3561761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3561761 prefixEnd_3561761 := by exact prefixLift 3561761
  have htrace : WordTrace (prefixWord ++ tailWord_3561761) baseStart_3561761 baseEnd_3561761 := by
    simpa [prefixWord, tailWord_3561761, baseEnd_3561761] using wordTrace_append hprefix tailTrace_3561761
  have hstable : (prefixWord ++ tailWord_3561761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561761).length < 2 ^ (prefixWord ++ tailWord_3561761).sum := by decide
  have hdescent : baseEnd_3561761 < baseStart_3561761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561788 : List Nat := [2, 2, 2, 2, 1, 2, 2, 1, 4, 1, 4]
def baseStart_3561788 : Nat := 118140960795 + 3561788 * 2 ^ 59
def prefixEnd_3561788 : Nat := 4983230072969 + 3 ^ 40 * 3561788 * 2
def baseEnd_3561788 : Nat := 1828909233416415721769641

theorem tailTrace_3561788 : CollatzResearch.WordTrace tailWord_3561788 prefixEnd_3561788 1828909233416415721769641 := by
  unfold tailWord_3561788
  simp only [CollatzResearch.WordTrace]
  refine ⟨64954540410128927902939009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86606053880171903870585345 64954540410128927902939009)
  ·
    refine ⟨48715905307596695927204257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64954540410128927902939009 48715905307596695927204257)
    ·
      refine ⟨36536928980697521945403193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48715905307596695927204257 36536928980697521945403193)
      ·
        refine ⟨27402696735523141459052395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36536928980697521945403193 27402696735523141459052395)
        ·
          refine ⟨41104045103284712188578593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27402696735523141459052395 41104045103284712188578593)
          ·
            refine ⟨30828033827463534141433945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41104045103284712188578593 30828033827463534141433945)
            ·
              refine ⟨23121025370597650606075459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30828033827463534141433945 23121025370597650606075459)
              ·
                refine ⟨34681538055896475909113189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23121025370597650606075459 34681538055896475909113189)
                ·
                  refine ⟨6502788385480589232958723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34681538055896475909113189 6502788385480589232958723)
                  ·
                    refine ⟨9754182578220883849438085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6502788385480589232958723 9754182578220883849438085)
                    ·
                      refine ⟨1828909233416415721769641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9754182578220883849438085 1828909233416415721769641)
                      ·
                        rfl

theorem cell23_3561788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_3561788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3561788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3561788 prefixEnd_3561788 := by exact prefixLift 3561788
  have htrace : WordTrace (prefixWord ++ tailWord_3561788) baseStart_3561788 baseEnd_3561788 := by
    simpa [prefixWord, tailWord_3561788, baseEnd_3561788] using wordTrace_append hprefix tailTrace_3561788
  have hstable : (prefixWord ++ tailWord_3561788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561788).length < 2 ^ (prefixWord ++ tailWord_3561788).sum := by decide
  have hdescent : baseEnd_3561788 < baseStart_3561788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561801 : List Nat := [1, 2, 1, 1, 2, 3, 1, 1, 4, 1, 6]
def baseStart_3561801 : Nat := 118140960795 + 3561801 * 2 ^ 59
def prefixEnd_3561801 : Nat := 4983230072969 + 3 ^ 40 * 3561801 * 2
def baseEnd_3561801 : Nat := 1828915908664924170907081

theorem tailTrace_3561801 : CollatzResearch.WordTrace tailWord_3561801 prefixEnd_3561801 1828915908664924170907081 := by
  unfold tailWord_3561801
  simp only [CollatzResearch.WordTrace]
  refine ⟨129909554969210759026101257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86606369979473839350734171 129909554969210759026101257)
  ·
    refine ⟨97432166226908069269575943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129909554969210759026101257 97432166226908069269575943)
    ·
      refine ⟨146148249340362103904363915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97432166226908069269575943 146148249340362103904363915)
      ·
        refine ⟨219222374010543155856545873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146148249340362103904363915 219222374010543155856545873)
        ·
          refine ⟨164416780507907366892409405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219222374010543155856545873 164416780507907366892409405)
          ·
            refine ⟨61656292690465262584653527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164416780507907366892409405 61656292690465262584653527)
            ·
              refine ⟨92484439035697893876980291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61656292690465262584653527 92484439035697893876980291)
              ·
                refine ⟨138726658553546840815470437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92484439035697893876980291 138726658553546840815470437)
                ·
                  refine ⟨26011248478790032652900707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138726658553546840815470437 26011248478790032652900707)
                  ·
                    refine ⟨39016872718185048979351061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26011248478790032652900707 39016872718185048979351061)
                    ·
                      refine ⟨1828915908664924170907081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39016872718185048979351061 1828915908664924170907081)
                      ·
                        rfl

theorem cell23_3561801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 1, 6].length) (baseStart_3561801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3561801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3561801 prefixEnd_3561801 := by exact prefixLift 3561801
  have htrace : WordTrace (prefixWord ++ tailWord_3561801) baseStart_3561801 baseEnd_3561801 := by
    simpa [prefixWord, tailWord_3561801, baseEnd_3561801] using wordTrace_append hprefix tailTrace_3561801
  have hstable : (prefixWord ++ tailWord_3561801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561801).length < 2 ^ (prefixWord ++ tailWord_3561801).sum := by decide
  have hdescent : baseEnd_3561801 < baseStart_3561801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561808 : List Nat := [2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 3]
def baseStart_3561808 : Nat := 118140960795 + 3561808 * 2 ^ 59
def prefixEnd_3561808 : Nat := 4983230072969 + 3 ^ 40 * 3561808 * 2
def baseEnd_3561808 : Nat := 1828919503029505643519549

theorem tailTrace_3561808 : CollatzResearch.WordTrace tailWord_3561808 prefixEnd_3561808 1828919503029505643519549 := by
  unfold tailWord_3561808
  simp only [CollatzResearch.WordTrace]
  refine ⟨64954905140092699610803039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86606540186790266147737385 64954905140092699610803039)
  ·
    refine ⟨97432357710139049416204559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64954905140092699610803039 97432357710139049416204559)
    ·
      refine ⟨146148536565208574124306839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97432357710139049416204559 146148536565208574124306839)
      ·
        refine ⟨219222804847812861186460259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146148536565208574124306839 219222804847812861186460259)
        ·
          refine ⟨328834207271719291779690389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219222804847812861186460259 328834207271719291779690389)
          ·
            refine ⟨15414103465861841802172987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 328834207271719291779690389 15414103465861841802172987)
            ·
              refine ⟨23121155198792762703259481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15414103465861841802172987 23121155198792762703259481)
              ·
                refine ⟨17340866399094572027444611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23121155198792762703259481 17340866399094572027444611)
                ·
                  refine ⟨26011299598641858041166917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17340866399094572027444611 26011299598641858041166917)
                  ·
                    refine ⟨4877118674745348382718797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26011299598641858041166917 4877118674745348382718797)
                    ·
                      refine ⟨1828919503029505643519549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4877118674745348382718797 1828919503029505643519549)
                      ·
                        rfl

theorem cell23_3561808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 3].length) (baseStart_3561808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3561808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3561808 prefixEnd_3561808 := by exact prefixLift 3561808
  have htrace : WordTrace (prefixWord ++ tailWord_3561808) baseStart_3561808 baseEnd_3561808 := by
    simpa [prefixWord, tailWord_3561808, baseEnd_3561808] using wordTrace_append hprefix tailTrace_3561808
  have hstable : (prefixWord ++ tailWord_3561808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561808).length < 2 ^ (prefixWord ++ tailWord_3561808).sum := by decide
  have hdescent : baseEnd_3561808 < baseStart_3561808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561882 : List Nat := [3, 1, 1, 4, 1, 2, 1, 3, 2, 3, 2]
def baseStart_3561882 : Nat := 118140960795 + 3561882 * 2 ^ 59
def prefixEnd_3561882 : Nat := 4983230072969 + 3 ^ 40 * 3561882 * 2
def baseEnd_3561882 : Nat := 1828957500597938353994209

theorem tailTrace_3561882 : CollatzResearch.WordTrace tailWord_3561882 prefixEnd_3561882 1828957500597938353994209 := by
  unfold tailWord_3561882
  simp only [CollatzResearch.WordTrace]
  refine ⟨32478127320479327464949975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86608339521278206573199933 32478127320479327464949975)
  ·
    refine ⟨48717190980718991197424963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32478127320479327464949975 48717190980718991197424963)
    ·
      refine ⟨73075786471078486796137445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48717190980718991197424963 73075786471078486796137445)
      ·
        refine ⟨13701709963327216274275771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73075786471078486796137445 13701709963327216274275771)
        ·
          refine ⟨20552564944990824411413657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13701709963327216274275771 20552564944990824411413657)
          ·
            refine ⟨15414423708743118308560243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20552564944990824411413657 15414423708743118308560243)
            ·
              refine ⟨23121635563114677462840365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15414423708743118308560243 23121635563114677462840365)
              ·
                refine ⟨8670613336168004048565137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23121635563114677462840365 8670613336168004048565137)
                ·
                  refine ⟨6502960002126003036423853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8670613336168004048565137 6502960002126003036423853)
                  ·
                    refine ⟨2438610000797251138658945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6502960002126003036423853 2438610000797251138658945)
                    ·
                      refine ⟨1828957500597938353994209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2438610000797251138658945 1828957500597938353994209)
                      ·
                        rfl

theorem cell23_3561882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_3561882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3561882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3561882 prefixEnd_3561882 := by exact prefixLift 3561882
  have htrace : WordTrace (prefixWord ++ tailWord_3561882) baseStart_3561882 baseEnd_3561882 := by
    simpa [prefixWord, tailWord_3561882, baseEnd_3561882] using wordTrace_append hprefix tailTrace_3561882
  have hstable : (prefixWord ++ tailWord_3561882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561882).length < 2 ^ (prefixWord ++ tailWord_3561882).sum := by decide
  have hdescent : baseEnd_3561882 < baseStart_3561882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561888 : List Nat := [2, 1, 1, 4, 1, 3, 1, 1, 3, 6]
def baseStart_3561888 : Nat := 118140960795 + 3561888 * 2 ^ 59
def prefixEnd_3561888 : Nat := 4983230072969 + 3 ^ 40 * 3561888 * 2
def baseEnd_3561888 : Nat := 609653527160621776839727

theorem tailTrace_3561888 : CollatzResearch.WordTrace tailWord_3561888 prefixEnd_3561888 609653527160621776839727 := by
  unfold tailWord_3561888
  simp only [CollatzResearch.WordTrace]
  refine ⟨64956364059947786442259159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86608485413263715256345545 64956364059947786442259159)
  ·
    refine ⟨97434546089921679663388739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64956364059947786442259159 97434546089921679663388739)
    ·
      refine ⟨146151819134882519495083109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97434546089921679663388739 146151819134882519495083109)
      ·
        refine ⟨27403466087790472405328083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146151819134882519495083109 27403466087790472405328083)
        ·
          refine ⟨41105199131685708607992125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27403466087790472405328083 41105199131685708607992125)
          ·
            refine ⟨15414449674382140727997047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41105199131685708607992125 15414449674382140727997047)
            ·
              refine ⟨23121674511573211091995571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15414449674382140727997047 23121674511573211091995571)
              ·
                refine ⟨34682511767359816637993357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23121674511573211091995571 34682511767359816637993357)
                ·
                  refine ⟨13005941912759931239247509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34682511767359816637993357 13005941912759931239247509)
                  ·
                    refine ⟨609653527160621776839727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13005941912759931239247509 609653527160621776839727)
                    ·
                      rfl

theorem cell23_3561888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 3, 6].length) (baseStart_3561888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3561888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3561888 prefixEnd_3561888 := by exact prefixLift 3561888
  have htrace : WordTrace (prefixWord ++ tailWord_3561888) baseStart_3561888 baseEnd_3561888 := by
    simpa [prefixWord, tailWord_3561888, baseEnd_3561888] using wordTrace_append hprefix tailTrace_3561888
  have hstable : (prefixWord ++ tailWord_3561888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561888).length < 2 ^ (prefixWord ++ tailWord_3561888).sum := by decide
  have hdescent : baseEnd_3561888 < baseStart_3561888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561912 : List Nat := [2, 1, 2, 1, 2, 2, 1, 5, 3, 2, 2]
def baseStart_3561912 : Nat := 118140960795 + 3561912 * 2 ^ 59
def prefixEnd_3561912 : Nat := 4983230072969 + 3 ^ 40 * 3561912 * 2
def baseEnd_3561912 : Nat := 1828972905017573236619071

theorem tailTrace_3561912 : CollatzResearch.WordTrace tailWord_3561912 prefixEnd_3561912 1828972905017573236619071 := by
  unfold tailWord_3561912
  simp only [CollatzResearch.WordTrace]
  refine ⟨64956801735904312491695995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86609068981205749988927993 64956801735904312491695995)
  ·
    refine ⟨97435202603856468737543993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64956801735904312491695995 97435202603856468737543993)
    ·
      refine ⟨73076401952892351553157995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97435202603856468737543993 73076401952892351553157995)
      ·
        refine ⟨109614602929338527329736993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73076401952892351553157995 109614602929338527329736993)
        ·
          refine ⟨82210952197003895497302745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109614602929338527329736993 82210952197003895497302745)
          ·
            refine ⟨61658214147752921622977059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82210952197003895497302745 61658214147752921622977059)
            ·
              refine ⟨92487321221629382434465589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61658214147752921622977059 92487321221629382434465589)
              ·
                refine ⟨8670686364527754603231149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92487321221629382434465589 8670686364527754603231149)
                ·
                  refine ⟨3251507386697907976211681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8670686364527754603231149 3251507386697907976211681)
                  ·
                    refine ⟨2438630540023430982158761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3251507386697907976211681 2438630540023430982158761)
                    ·
                      refine ⟨1828972905017573236619071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2438630540023430982158761 1828972905017573236619071)
                      ·
                        rfl

theorem cell23_3561912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5, 3, 2, 2].length) (baseStart_3561912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3561912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3561912 prefixEnd_3561912 := by exact prefixLift 3561912
  have htrace : WordTrace (prefixWord ++ tailWord_3561912) baseStart_3561912 baseEnd_3561912 := by
    simpa [prefixWord, tailWord_3561912, baseEnd_3561912] using wordTrace_append hprefix tailTrace_3561912
  have hstable : (prefixWord ++ tailWord_3561912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561912).length < 2 ^ (prefixWord ++ tailWord_3561912).sum := by decide
  have hdescent : baseEnd_3561912 < baseStart_3561912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561942 : List Nat := [5, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4]
def baseStart_3561942 : Nat := 118140960795 + 3561942 * 2 ^ 59
def prefixEnd_3561942 : Nat := 4983230072969 + 3 ^ 40 * 3561942 * 2
def baseEnd_3561942 : Nat := 1828988309437208119243933

theorem tailTrace_3561942 : CollatzResearch.WordTrace tailWord_3561942 prefixEnd_3561942 1828988309437208119243933 := by
  unfold tailWord_3561942
  simp only [CollatzResearch.WordTrace]
  refine ⟨8119668603856246256686505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86609798441133293404656053 8119668603856246256686505)
  ·
    refine ⟨6089751452892184692514879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8119668603856246256686505 6089751452892184692514879)
    ·
      refine ⟨9134627179338277038772319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6089751452892184692514879 9134627179338277038772319)
      ·
        refine ⟨13701940769007415558158479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9134627179338277038772319 13701940769007415558158479)
        ·
          refine ⟨20552911153511123337237719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13701940769007415558158479 20552911153511123337237719)
          ·
            refine ⟨30829366730266685005856579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20552911153511123337237719 30829366730266685005856579)
            ·
              refine ⟨46244050095400027508784869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30829366730266685005856579 46244050095400027508784869)
              ·
                refine ⟨8670759392887505157897163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46244050095400027508784869 8670759392887505157897163)
                ·
                  refine ⟨13006139089331257736845745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8670759392887505157897163 13006139089331257736845745)
                  ·
                    refine ⟨9754604316998443302634309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13006139089331257736845745 9754604316998443302634309)
                    ·
                      refine ⟨1828988309437208119243933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9754604316998443302634309 1828988309437208119243933)
                      ·
                        rfl

theorem cell23_3561942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_3561942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3561942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3561942 prefixEnd_3561942 := by exact prefixLift 3561942
  have htrace : WordTrace (prefixWord ++ tailWord_3561942) baseStart_3561942 baseEnd_3561942 := by
    simpa [prefixWord, tailWord_3561942, baseEnd_3561942] using wordTrace_append hprefix tailTrace_3561942
  have hstable : (prefixWord ++ tailWord_3561942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561942).length < 2 ^ (prefixWord ++ tailWord_3561942).sum := by decide
  have hdescent : baseEnd_3561942 < baseStart_3561942 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561945 : List Nat := [1, 2, 1, 2, 4, 1, 1, 4, 1, 3, 3]
def baseStart_3561945 : Nat := 118140960795 + 3561945 * 2 ^ 59
def prefixEnd_3561945 : Nat := 4983230072969 + 3 ^ 40 * 3561945 * 2
def baseEnd_3561945 : Nat := 1828989849879171607506419

theorem tailTrace_3561945 : CollatzResearch.WordTrace tailWord_3561945 prefixEnd_3561945 1828989849879171607506419 := by
  unfold tailWord_3561945
  simp only [CollatzResearch.WordTrace]
  refine ⟨129914807080689071619343289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86609871387126047746228859 129914807080689071619343289)
  ·
    refine ⟨97436105310516803714507467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129914807080689071619343289 97436105310516803714507467)
    ·
      refine ⟨146154157965775205571761201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97436105310516803714507467 146154157965775205571761201)
      ·
        refine ⟨109615618474331404178820901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146154157965775205571761201 109615618474331404178820901)
        ·
          refine ⟨20552928463937138283528919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109615618474331404178820901 20552928463937138283528919)
          ·
            refine ⟨30829392695905707425293379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20552928463937138283528919 30829392695905707425293379)
            ·
              refine ⟨46244089043858561137940069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30829392695905707425293379 46244089043858561137940069)
              ·
                refine ⟨8670766695723480213363763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46244089043858561137940069 8670766695723480213363763)
                ·
                  refine ⟨13006150043585220320045645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8670766695723480213363763 13006150043585220320045645)
                  ·
                    refine ⟨4877306266344457620017117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13006150043585220320045645 4877306266344457620017117)
                    ·
                      refine ⟨1828989849879171607506419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4877306266344457620017117 1828989849879171607506419)
                      ·
                        rfl

theorem cell23_3561945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4, 1, 3, 3].length) (baseStart_3561945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3561945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3561945 prefixEnd_3561945 := by exact prefixLift 3561945
  have htrace : WordTrace (prefixWord ++ tailWord_3561945) baseStart_3561945 baseEnd_3561945 := by
    simpa [prefixWord, tailWord_3561945, baseEnd_3561945] using wordTrace_append hprefix tailTrace_3561945
  have hstable : (prefixWord ++ tailWord_3561945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561945).length < 2 ^ (prefixWord ++ tailWord_3561945).sum := by decide
  have hdescent : baseEnd_3561945 < baseStart_3561945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561946 : List Nat := [3, 1, 1, 2, 3, 1, 4, 3, 1, 2, 2]
def baseStart_3561946 : Nat := 118140960795 + 3561946 * 2 ^ 59
def prefixEnd_3561946 : Nat := 4983230072969 + 3 ^ 40 * 3561946 * 2
def baseEnd_3561946 : Nat := 1828990363359826103593915

theorem tailTrace_3561946 : CollatzResearch.WordTrace tailWord_3561946 prefixEnd_3561946 1828990363359826103593915 := by
  unfold tailWord_3561946
  simp only [CollatzResearch.WordTrace]
  refine ⟨32478710888421362197532423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86609895702456965860086461 32478710888421362197532423)
  ·
    refine ⟨48718066332632043296298635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32478710888421362197532423 48718066332632043296298635)
    ·
      refine ⟨73077099498948064944447953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48718066332632043296298635 73077099498948064944447953)
      ·
        refine ⟨54807824624211048708335965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73077099498948064944447953 54807824624211048708335965)
        ·
          refine ⟨20552934234079143265625987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54807824624211048708335965 20552934234079143265625987)
          ·
            refine ⟨30829401351118714898438981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20552934234079143265625987 30829401351118714898438981)
            ·
              refine ⟨5780512753334759043457309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30829401351118714898438981 5780512753334759043457309)
              ·
                refine ⟨2167692282500534641296491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5780512753334759043457309 2167692282500534641296491)
                ·
                  refine ⟨3251538423750801961944737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2167692282500534641296491 3251538423750801961944737)
                  ·
                    refine ⟨2438653817813101471458553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3251538423750801961944737 2438653817813101471458553)
                    ·
                      refine ⟨1828990363359826103593915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2438653817813101471458553 1828990363359826103593915)
                      ·
                        rfl

theorem cell23_3561946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 3, 1, 2, 2].length) (baseStart_3561946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3561946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3561946 prefixEnd_3561946 := by exact prefixLift 3561946
  have htrace : WordTrace (prefixWord ++ tailWord_3561946) baseStart_3561946 baseEnd_3561946 := by
    simpa [prefixWord, tailWord_3561946, baseEnd_3561946] using wordTrace_append hprefix tailTrace_3561946
  have hstable : (prefixWord ++ tailWord_3561946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561946).length < 2 ^ (prefixWord ++ tailWord_3561946).sum := by decide
  have hdescent : baseEnd_3561946 < baseStart_3561946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561978 : List Nat := [3, 1, 1, 1, 1, 2, 2, 3, 1, 8]
def baseStart_3561978 : Nat := 118140960795 + 3561978 * 2 ^ 59
def prefixEnd_3561978 : Nat := 4983230072969 + 3 ^ 40 * 3561978 * 2
def baseEnd_3561978 : Nat := 609668931580256659464589

theorem tailTrace_3561978 : CollatzResearch.WordTrace tailWord_3561978 prefixEnd_3561978 609668931580256659464589 := by
  unfold tailWord_3561978
  simp only [CollatzResearch.WordTrace]
  refine ⟨32479002672392379563823647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86610673793046345503529725 32479002672392379563823647)
  ·
    refine ⟨48718504008588569345735471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32479002672392379563823647 48718504008588569345735471)
    ·
      refine ⟨73077756012882854018603207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48718504008588569345735471 73077756012882854018603207)
      ·
        refine ⟨109616634019324281027904811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73077756012882854018603207 109616634019324281027904811)
        ·
          refine ⟨164424951028986421541857217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109616634019324281027904811 164424951028986421541857217)
          ·
            refine ⟨123318713271739816156392913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164424951028986421541857217 123318713271739816156392913)
            ·
              refine ⟨92489034953804862117294685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123318713271739816156392913 92489034953804862117294685)
              ·
                refine ⟨34683388107676823293985507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92489034953804862117294685 34683388107676823293985507)
                ·
                  refine ⟨52025082161515234940978261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34683388107676823293985507 52025082161515234940978261)
                  ·
                    refine ⟨609668931580256659464589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 52025082161515234940978261 609668931580256659464589)
                    ·
                      rfl

theorem cell23_3561978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 1, 8].length) (baseStart_3561978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3561978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3561978 prefixEnd_3561978 := by exact prefixLift 3561978
  have htrace : WordTrace (prefixWord ++ tailWord_3561978) baseStart_3561978 baseEnd_3561978 := by
    simpa [prefixWord, tailWord_3561978, baseEnd_3561978] using wordTrace_append hprefix tailTrace_3561978
  have hstable : (prefixWord ++ tailWord_3561978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561978).length < 2 ^ (prefixWord ++ tailWord_3561978).sum := by decide
  have hdescent : baseEnd_3561978 < baseStart_3561978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561986 : List Nat := [3, 4, 1, 2, 3, 1, 2, 7]
def baseStart_3561986 : Nat := 118140960795 + 3561986 * 2 ^ 59
def prefixEnd_3561986 : Nat := 4983230072969 + 3 ^ 40 * 3561986 * 2
def baseEnd_3561986 : Nat := 67741144540222442484953

theorem tailTrace_3561986 : CollatzResearch.WordTrace tailWord_3561986 prefixEnd_3561986 67741144540222442484953 := by
  unfold tailWord_3561986
  simp only [CollatzResearch.WordTrace]
  refine ⟨32479075618385133905396453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86610868315693690414390541 32479075618385133905396453)
  ·
    refine ⟨6089826678447212607261835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32479075618385133905396453 6089826678447212607261835)
    ·
      refine ⟨9134740017670818910892753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6089826678447212607261835 9134740017670818910892753)
      ·
        refine ⟨6851055013253114183169565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9134740017670818910892753 6851055013253114183169565)
        ·
          refine ⟨2569145629969917818688587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6851055013253114183169565 2569145629969917818688587)
          ·
            refine ⟨3853718444954876728032881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2569145629969917818688587 3853718444954876728032881)
            ·
              refine ⟨2890288833716157546024661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3853718444954876728032881 2890288833716157546024661)
              ·
                refine ⟨67741144540222442484953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2890288833716157546024661 67741144540222442484953)
                ·
                  rfl

theorem cell23_3561986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 7].length) (baseStart_3561986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3561986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3561986 prefixEnd_3561986 := by exact prefixLift 3561986
  have htrace : WordTrace (prefixWord ++ tailWord_3561986) baseStart_3561986 baseEnd_3561986 := by
    simpa [prefixWord, tailWord_3561986, baseEnd_3561986] using wordTrace_append hprefix tailTrace_3561986
  have hstable : (prefixWord ++ tailWord_3561986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561986).length < 2 ^ (prefixWord ++ tailWord_3561986).sum := by decide
  have hdescent : baseEnd_3561986 < baseStart_3561986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3561997 : List Nat := [1, 7, 1, 1, 1, 3, 1, 3, 1, 2, 2]
def baseStart_3561997 : Nat := 118140960795 + 3561997 * 2 ^ 59
def prefixEnd_3561997 : Nat := 4983230072969 + 3 ^ 40 * 3561997 * 2
def baseEnd_3561997 : Nat := 1829016550873205404056181

theorem tailTrace_3561997 : CollatzResearch.WordTrace tailWord_3561997 prefixEnd_3561997 1829016550873205404056181 := by
  unfold tailWord_3561997
  simp only [CollatzResearch.WordTrace]
  refine ⟨129916703676500684500236245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86611135784333789666824163 129916703676500684500236245)
  ·
    refine ⟨3044922742417984792974287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 129916703676500684500236245 3044922742417984792974287)
    ·
      refine ⟨4567384113626977189461431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3044922742417984792974287 4567384113626977189461431)
      ·
        refine ⟨6851076170440465784192147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4567384113626977189461431 6851076170440465784192147)
        ·
          refine ⟨10276614255660698676288221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6851076170440465784192147 10276614255660698676288221)
          ·
            refine ⟨3853730345872762003608083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10276614255660698676288221 3853730345872762003608083)
            ·
              refine ⟨5780595518809143005412125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3853730345872762003608083 5780595518809143005412125)
              ·
                refine ⟨2167723319553428627029547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5780595518809143005412125 2167723319553428627029547)
                ·
                  refine ⟨3251584979330142940544321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2167723319553428627029547 3251584979330142940544321)
                  ·
                    refine ⟨2438688734497607205408241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3251584979330142940544321 2438688734497607205408241)
                    ·
                      refine ⟨1829016550873205404056181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2438688734497607205408241 1829016550873205404056181)
                      ·
                        rfl

theorem cell23_3561997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_3561997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3561997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3561997 prefixEnd_3561997 := by exact prefixLift 3561997
  have htrace : WordTrace (prefixWord ++ tailWord_3561997) baseStart_3561997 baseEnd_3561997 := by
    simpa [prefixWord, tailWord_3561997, baseEnd_3561997] using wordTrace_append hprefix tailTrace_3561997
  have hstable : (prefixWord ++ tailWord_3561997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3561997).length < 2 ^ (prefixWord ++ tailWord_3561997).sum := by decide
  have hdescent : baseEnd_3561997 < baseStart_3561997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3561997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562005 : List Nat := [1, 3, 2, 1, 3, 1, 3, 1, 2, 1, 5]
def baseStart_3562005 : Nat := 118140960795 + 3562005 * 2 ^ 59
def prefixEnd_3562005 : Nat := 4983230072969 + 3 ^ 40 * 3562005 * 2
def baseEnd_3562005 : Nat := 1829020658718441372756143

theorem tailTrace_3562005 : CollatzResearch.WordTrace tailWord_3562005 prefixEnd_3562005 1829020658718441372756143 := by
  unfold tailWord_3562005
  simp only [CollatzResearch.WordTrace]
  refine ⟨129916995460471701866527469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86611330306981134577684979 129916995460471701866527469)
  ·
    refine ⟨48718873297676888199947801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129916995460471701866527469 48718873297676888199947801)
    ·
      refine ⟨36539154973257666149960851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48718873297676888199947801 36539154973257666149960851)
      ·
        refine ⟨54808732459886499224941277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36539154973257666149960851 54808732459886499224941277)
        ·
          refine ⟨20553274672457437209352979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54808732459886499224941277 20553274672457437209352979)
          ·
            refine ⟨30829912008686155814029469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20553274672457437209352979 30829912008686155814029469)
            ·
              refine ⟨11561217003257308430261051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30829912008686155814029469 11561217003257308430261051)
              ·
                refine ⟨17341825504885962645391577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11561217003257308430261051 17341825504885962645391577)
                ·
                  refine ⟨13006369128664471984043683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17341825504885962645391577 13006369128664471984043683)
                  ·
                    refine ⟨19509553692996707976065525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13006369128664471984043683 19509553692996707976065525)
                    ·
                      refine ⟨1829020658718441372756143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19509553692996707976065525 1829020658718441372756143)
                      ·
                        rfl

theorem cell23_3562005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_3562005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3562005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3562005 prefixEnd_3562005 := by exact prefixLift 3562005
  have htrace : WordTrace (prefixWord ++ tailWord_3562005) baseStart_3562005 baseEnd_3562005 := by
    simpa [prefixWord, tailWord_3562005, baseEnd_3562005] using wordTrace_append hprefix tailTrace_3562005
  have hstable : (prefixWord ++ tailWord_3562005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562005).length < 2 ^ (prefixWord ++ tailWord_3562005).sum := by decide
  have hdescent : baseEnd_3562005 < baseStart_3562005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562019 : List Nat := [1, 1, 1, 4, 4, 1, 2, 1, 4, 2, 2]
def baseStart_3562019 : Nat := 118140960795 + 3562019 * 2 ^ 59
def prefixEnd_3562019 : Nat := 4983230072969 + 3 ^ 40 * 3562019 * 2
def baseEnd_3562019 : Nat := 1829027847447604317981079

theorem tailTrace_3562019 : CollatzResearch.WordTrace tailWord_3562019 prefixEnd_3562019 1829027847447604317981079 := by
  unfold tailWord_3562019
  simp only [CollatzResearch.WordTrace]
  refine ⟨129917506082420982257537111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86611670721613988171691407 129917506082420982257537111)
  ·
    refine ⟨194876259123631473386305667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129917506082420982257537111 194876259123631473386305667)
    ·
      refine ⟨292314388685447210079458501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194876259123631473386305667 292314388685447210079458501)
      ·
        refine ⟨54808947878521351889898469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 292314388685447210079458501 54808947878521351889898469)
        ·
          refine ⟨10276677727222753479355963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54808947878521351889898469 10276677727222753479355963)
          ·
            refine ⟨15415016590834130219033945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10276677727222753479355963 15415016590834130219033945)
            ·
              refine ⟨11561262443125597664275459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15415016590834130219033945 11561262443125597664275459)
              ·
                refine ⟨17341893664688396496413189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11561262443125597664275459 17341893664688396496413189)
                ·
                  refine ⟨3251605062129074343077473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17341893664688396496413189 3251605062129074343077473)
                  ·
                    refine ⟨2438703796596805757308105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3251605062129074343077473 2438703796596805757308105)
                    ·
                      refine ⟨1829027847447604317981079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2438703796596805757308105 1829027847447604317981079)
                      ·
                        rfl

theorem cell23_3562019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 4, 2, 2].length) (baseStart_3562019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3562019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3562019 prefixEnd_3562019 := by exact prefixLift 3562019
  have htrace : WordTrace (prefixWord ++ tailWord_3562019) baseStart_3562019 baseEnd_3562019 := by
    simpa [prefixWord, tailWord_3562019, baseEnd_3562019] using wordTrace_append hprefix tailTrace_3562019
  have hstable : (prefixWord ++ tailWord_3562019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562019).length < 2 ^ (prefixWord ++ tailWord_3562019).sum := by decide
  have hdescent : baseEnd_3562019 < baseStart_3562019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562030 : List Nat := [4, 1, 3, 1, 4, 1, 2, 1, 2, 1, 3]
def baseStart_3562030 : Nat := 118140960795 + 3562030 * 2 ^ 59
def prefixEnd_3562030 : Nat := 4983230072969 + 3 ^ 40 * 3562030 * 2
def baseEnd_3562030 : Nat := 1829033495734803774943529

theorem tailTrace_3562030 : CollatzResearch.WordTrace tailWord_3562030 prefixEnd_3562030 1829033495734803774943529 := by
  unfold tailWord_3562030
  simp only [CollatzResearch.WordTrace]
  refine ⟨16239738410672641392023443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86611938190254087424125029 16239738410672641392023443)
  ·
    refine ⟨24359607616008962088035165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16239738410672641392023443 24359607616008962088035165)
    ·
      refine ⟨9134852856003360783013187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24359607616008962088035165 9134852856003360783013187)
      ·
        refine ⟨13702279284005041174519781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9134852856003360783013187 13702279284005041174519781)
        ·
          refine ⟨2569177365750945220222459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13702279284005041174519781 2569177365750945220222459)
          ·
            refine ⟨3853766048626417830333689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2569177365750945220222459 3853766048626417830333689)
            ·
              refine ⟨2890324536469813372750267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3853766048626417830333689 2890324536469813372750267)
              ·
                refine ⟨4335486804704720059125401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2890324536469813372750267 4335486804704720059125401)
                ·
                  refine ⟨3251615103528540044344051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4335486804704720059125401 3251615103528540044344051)
                  ·
                    refine ⟨4877422655292810066516077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3251615103528540044344051 4877422655292810066516077)
                    ·
                      refine ⟨1829033495734803774943529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4877422655292810066516077 1829033495734803774943529)
                      ·
                        rfl

theorem cell23_3562030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_3562030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3562030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3562030 prefixEnd_3562030 := by exact prefixLift 3562030
  have htrace : WordTrace (prefixWord ++ tailWord_3562030) baseStart_3562030 baseEnd_3562030 := by
    simpa [prefixWord, tailWord_3562030, baseEnd_3562030] using wordTrace_append hprefix tailTrace_3562030
  have hstable : (prefixWord ++ tailWord_3562030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562030).length < 2 ^ (prefixWord ++ tailWord_3562030).sum := by decide
  have hdescent : baseEnd_3562030 < baseStart_3562030 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562035 : List Nat := [1, 1, 1, 2, 4, 2, 2, 1, 1, 5, 3]
def baseStart_3562035 : Nat := 118140960795 + 3562035 * 2 ^ 59
def prefixEnd_3562035 : Nat := 4983230072969 + 3 ^ 40 * 3562035 * 2
def baseEnd_3562035 : Nat := 1829036063138076255381005

theorem tailTrace_3562035 : CollatzResearch.WordTrace tailWord_3562035 prefixEnd_3562035 1829036063138076255381005 := by
  unfold tailWord_3562035
  simp only [CollatzResearch.WordTrace]
  refine ⟨129918089650363016990119559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86612059766908677993413039 129918089650363016990119559)
  ·
    refine ⟨194877134475544525485179339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129918089650363016990119559 194877134475544525485179339)
    ·
      refine ⟨292315701713316788227769009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194877134475544525485179339 292315701713316788227769009)
      ·
        refine ⟨219236776284987591170826757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292315701713316788227769009 219236776284987591170826757)
        ·
          refine ⟨41106895553435173344530017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 219236776284987591170826757 41106895553435173344530017)
          ·
            refine ⟨30830171665076380008397513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41106895553435173344530017 30830171665076380008397513)
            ·
              refine ⟨23122628748807285006298135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30830171665076380008397513 23122628748807285006298135)
              ·
                refine ⟨34683943123210927509447203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23122628748807285006298135 34683943123210927509447203)
                ·
                  refine ⟨52025914684816391264170805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34683943123210927509447203 52025914684816391264170805)
                  ·
                    refine ⟨4877429501701536681016013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52025914684816391264170805 4877429501701536681016013)
                    ·
                      refine ⟨1829036063138076255381005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4877429501701536681016013 1829036063138076255381005)
                      ·
                        rfl

theorem cell23_3562035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 5, 3].length) (baseStart_3562035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3562035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3562035 prefixEnd_3562035 := by exact prefixLift 3562035
  have htrace : WordTrace (prefixWord ++ tailWord_3562035) baseStart_3562035 baseEnd_3562035 := by
    simpa [prefixWord, tailWord_3562035, baseEnd_3562035] using wordTrace_append hprefix tailTrace_3562035
  have hstable : (prefixWord ++ tailWord_3562035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562035).length < 2 ^ (prefixWord ++ tailWord_3562035).sum := by decide
  have hdescent : baseEnd_3562035 < baseStart_3562035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562065 : List Nat := [1, 2, 2, 1, 3, 3, 1, 2, 1, 2, 5]
def baseStart_3562065 : Nat := 118140960795 + 3562065 * 2 ^ 59
def prefixEnd_3562065 : Nat := 4983230072969 + 3 ^ 40 * 3562065 * 2
def baseEnd_3562065 : Nat := 1829051467557711138005867

theorem tailTrace_3562065 : CollatzResearch.WordTrace tailWord_3562065 prefixEnd_3562065 1829051467557711138005867 := by
  unfold tailWord_3562065
  simp only [CollatzResearch.WordTrace]
  refine ⟨129919183840254332113711649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86612789226836221409141099 129919183840254332113711649)
  ·
    refine ⟨97439387880190749085283737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129919183840254332113711649 97439387880190749085283737)
    ·
      refine ⟨73079540910143061813962803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97439387880190749085283737 73079540910143061813962803)
      ·
        refine ⟨109619311365214592720944205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73079540910143061813962803 109619311365214592720944205)
        ·
          refine ⟨41107241761955472270354077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109619311365214592720944205 41107241761955472270354077)
          ·
            refine ⟨15415215660733302101382779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41107241761955472270354077 15415215660733302101382779)
            ·
              refine ⟨23122823491099953152074169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15415215660733302101382779 23122823491099953152074169)
              ·
                refine ⟨17342117618324964864055627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23122823491099953152074169 17342117618324964864055627)
                ·
                  refine ⟨26013176427487447296083441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17342117618324964864055627 26013176427487447296083441)
                  ·
                    refine ⟨19509882320615585472062581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26013176427487447296083441 19509882320615585472062581)
                    ·
                      refine ⟨1829051467557711138005867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19509882320615585472062581 1829051467557711138005867)
                      ·
                        rfl

theorem cell23_3562065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 2, 5].length) (baseStart_3562065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3562065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3562065 prefixEnd_3562065 := by exact prefixLift 3562065
  have htrace : WordTrace (prefixWord ++ tailWord_3562065) baseStart_3562065 baseEnd_3562065 := by
    simpa [prefixWord, tailWord_3562065, baseEnd_3562065] using wordTrace_append hprefix tailTrace_3562065
  have hstable : (prefixWord ++ tailWord_3562065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562065).length < 2 ^ (prefixWord ++ tailWord_3562065).sum := by decide
  have hdescent : baseEnd_3562065 < baseStart_3562065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562092 : List Nat := [2, 2, 1, 1, 3, 1, 3, 1, 1, 6, 2]
def baseStart_3562092 : Nat := 118140960795 + 3562092 * 2 ^ 59
def prefixEnd_3562092 : Nat := 4983230072969 + 3 ^ 40 * 3562092 * 2
def baseEnd_3562092 : Nat := 1829065331535382532368243

theorem tailTrace_3562092 : CollatzResearch.WordTrace tailWord_3562092 prefixEnd_3562092 1829065331535382532368243 := by
  unfold tailWord_3562092
  simp only [CollatzResearch.WordTrace]
  refine ⟨64960084305578257862472265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86613445740771010483296353 64960084305578257862472265)
  ·
    refine ⟨48720063229183693396854199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64960084305578257862472265 48720063229183693396854199)
    ·
      refine ⟨73080094843775540095281299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48720063229183693396854199 73080094843775540095281299)
      ·
        refine ⟨109620142265663310142921949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73080094843775540095281299 109620142265663310142921949)
        ·
          refine ⟨41107553349623741303595731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109620142265663310142921949 41107553349623741303595731)
          ·
            refine ⟨61661330024435611955393597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41107553349623741303595731 61661330024435611955393597)
            ·
              refine ⟨23122998759163354483272599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61661330024435611955393597 23122998759163354483272599)
              ·
                refine ⟨34684498138745031724908899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23122998759163354483272599 34684498138745031724908899)
                ·
                  refine ⟨52026747208117547587363349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34684498138745031724908899 52026747208117547587363349)
                  ·
                    refine ⟨2438753775380510043157657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 52026747208117547587363349 2438753775380510043157657)
                    ·
                      refine ⟨1829065331535382532368243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2438753775380510043157657 1829065331535382532368243)
                      ·
                        rfl

theorem cell23_3562092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 6, 2].length) (baseStart_3562092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3562092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3562092 prefixEnd_3562092 := by exact prefixLift 3562092
  have htrace : WordTrace (prefixWord ++ tailWord_3562092) baseStart_3562092 baseEnd_3562092 := by
    simpa [prefixWord, tailWord_3562092, baseEnd_3562092] using wordTrace_append hprefix tailTrace_3562092
  have hstable : (prefixWord ++ tailWord_3562092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562092).length < 2 ^ (prefixWord ++ tailWord_3562092).sum := by decide
  have hdescent : baseEnd_3562092 < baseStart_3562092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562112 : List Nat := [2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 3]
def baseStart_3562112 : Nat := 118140960795 + 3562112 * 2 ^ 59
def prefixEnd_3562112 : Nat := 4983230072969 + 3 ^ 40 * 3562112 * 2
def baseEnd_3562112 : Nat := 1829075601148472454118151

theorem tailTrace_3562112 : CollatzResearch.WordTrace tailWord_3562112 prefixEnd_3562112 1829075601148472454118151 := by
  unfold tailWord_3562112
  simp only [CollatzResearch.WordTrace]
  refine ⟨64960449035542029570336295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86613932047389372760448393 64960449035542029570336295)
  ·
    refine ⟨97440673553313044355504443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64960449035542029570336295 97440673553313044355504443)
    ·
      refine ⟨146161010329969566533256665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97440673553313044355504443 146161010329969566533256665)
      ·
        refine ⟨109620757747477174899942499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146161010329969566533256665 109620757747477174899942499)
        ·
          refine ⟨164431136621215762349913749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109620757747477174899942499 164431136621215762349913749)
          ·
            refine ⟨7707709529119488860152207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 164431136621215762349913749 7707709529119488860152207)
            ·
              refine ⟨11561564293679233290228311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7707709529119488860152207 11561564293679233290228311)
              ·
                refine ⟨17342346440518849935342467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11561564293679233290228311 17342346440518849935342467)
                ·
                  refine ⟨26013519660778274903013701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17342346440518849935342467 26013519660778274903013701)
                  ·
                    refine ⟨4877534936395926544315069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26013519660778274903013701 4877534936395926544315069)
                    ·
                      refine ⟨1829075601148472454118151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4877534936395926544315069 1829075601148472454118151)
                      ·
                        rfl

theorem cell23_3562112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 3].length) (baseStart_3562112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3562112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3562112 prefixEnd_3562112 := by exact prefixLift 3562112
  have htrace : WordTrace (prefixWord ++ tailWord_3562112) baseStart_3562112 baseEnd_3562112 := by
    simpa [prefixWord, tailWord_3562112, baseEnd_3562112] using wordTrace_append hprefix tailTrace_3562112
  have hstable : (prefixWord ++ tailWord_3562112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562112).length < 2 ^ (prefixWord ++ tailWord_3562112).sum := by decide
  have hdescent : baseEnd_3562112 < baseStart_3562112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562135 : List Nat := [1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 8]
def baseStart_3562135 : Nat := 118140960795 + 3562135 * 2 ^ 59
def prefixEnd_3562135 : Nat := 4983230072969 + 3 ^ 40 * 3562135 * 2
def baseEnd_3562135 : Nat := 1829087411203525864130545

theorem tailTrace_3562135 : CollatzResearch.WordTrace tailWord_3562135 prefixEnd_3562135 1829087411203525864130545 := by
  unfold tailWord_3562135
  simp only [CollatzResearch.WordTrace]
  refine ⟨129921736950000734068759859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86614491300000489379173239 129921736950000734068759859)
  ·
    refine ⟨194882605425001101103139789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129921736950000734068759859 194882605425001101103139789)
    ·
      refine ⟨73080977034375412913677421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194882605425001101103139789 73080977034375412913677421)
      ·
        refine ⟨27405366387890779842629033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73080977034375412913677421 27405366387890779842629033)
        ·
          refine ⟨20554024790918084881971775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27405366387890779842629033 20554024790918084881971775)
          ·
            refine ⟨30831037186377127322957663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20554024790918084881971775 30831037186377127322957663)
            ·
              refine ⟨46246555779565690984436495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30831037186377127322957663 46246555779565690984436495)
              ·
                refine ⟨69369833669348536476654743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46246555779565690984436495 69369833669348536476654743)
                ·
                  refine ⟨104054750504022804714982115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69369833669348536476654743 104054750504022804714982115)
                  ·
                    refine ⟨156082125756034207072473173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 104054750504022804714982115 156082125756034207072473173)
                    ·
                      refine ⟨1829087411203525864130545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 156082125756034207072473173 1829087411203525864130545)
                      ·
                        rfl

theorem cell23_3562135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_3562135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3562135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3562135 prefixEnd_3562135 := by exact prefixLift 3562135
  have htrace : WordTrace (prefixWord ++ tailWord_3562135) baseStart_3562135 baseEnd_3562135 := by
    simpa [prefixWord, tailWord_3562135, baseEnd_3562135] using wordTrace_append hprefix tailTrace_3562135
  have hstable : (prefixWord ++ tailWord_3562135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562135).length < 2 ^ (prefixWord ++ tailWord_3562135).sum := by decide
  have hdescent : baseEnd_3562135 < baseStart_3562135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562159 : List Nat := [1, 1, 2, 1, 2, 5, 2, 2, 3, 1, 3]
def baseStart_3562159 : Nat := 118140960795 + 3562159 * 2 ^ 59
def prefixEnd_3562159 : Nat := 4983230072969 + 3 ^ 40 * 3562159 * 2
def baseEnd_3562159 : Nat := 1829099734739233770230435

theorem tailTrace_3562159 : CollatzResearch.WordTrace tailWord_3562159 prefixEnd_3562159 1829099734739233770230435 := by
  unfold tailWord_3562159
  simp only [CollatzResearch.WordTrace]
  refine ⟨129922612301913786167633531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86615074867942524111755687 129922612301913786167633531)
  ·
    refine ⟨194883918452870679251450297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129922612301913786167633531 194883918452870679251450297)
    ·
      refine ⟨146162938839653009438587723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194883918452870679251450297 146162938839653009438587723)
      ·
        refine ⟨219244408259479514157881585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146162938839653009438587723 219244408259479514157881585)
        ·
          refine ⟨164433306194609635618411189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219244408259479514157881585 164433306194609635618411189)
          ·
            refine ⟨15415622455744653339226049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 164433306194609635618411189 15415622455744653339226049)
            ·
              refine ⟨11561716841808490004419537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15415622455744653339226049 11561716841808490004419537)
              ·
                refine ⟨8671287631356367503314653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11561716841808490004419537 8671287631356367503314653)
                ·
                  refine ⟨3251732861758637813742995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8671287631356367503314653 3251732861758637813742995)
                  ·
                    refine ⟨4877599292637956720614493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3251732861758637813742995 4877599292637956720614493)
                    ·
                      refine ⟨1829099734739233770230435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4877599292637956720614493 1829099734739233770230435)
                      ·
                        rfl

theorem cell23_3562159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2, 3, 1, 3].length) (baseStart_3562159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3562159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3562159 prefixEnd_3562159 := by exact prefixLift 3562159
  have htrace : WordTrace (prefixWord ++ tailWord_3562159) baseStart_3562159 baseEnd_3562159 := by
    simpa [prefixWord, tailWord_3562159, baseEnd_3562159] using wordTrace_append hprefix tailTrace_3562159
  have hstable : (prefixWord ++ tailWord_3562159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562159).length < 2 ^ (prefixWord ++ tailWord_3562159).sum := by decide
  have hdescent : baseEnd_3562159 < baseStart_3562159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562169 : List Nat := [1, 2, 1, 4, 1, 1, 1, 5, 2, 3, 2]
def baseStart_3562169 : Nat := 118140960795 + 3562169 * 2 ^ 59
def prefixEnd_3562169 : Nat := 4983230072969 + 3 ^ 40 * 3562169 * 2
def baseEnd_3562169 : Nat := 1829104869545778731105389

theorem tailTrace_3562169 : CollatzResearch.WordTrace tailWord_3562169 prefixEnd_3562169 1829104869545778731105389 := by
  unfold tailWord_3562169
  simp only [CollatzResearch.WordTrace]
  refine ⟨129922977031877557875497561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86615318021251705250331707 129922977031877557875497561)
  ·
    refine ⟨97442232773908168406623171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129922977031877557875497561 97442232773908168406623171)
    ·
      refine ⟨146163349160862252609934757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97442232773908168406623171 146163349160862252609934757)
      ·
        refine ⟨27405627967661672364362767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146163349160862252609934757 27405627967661672364362767)
        ·
          refine ⟨41108441951492508546544151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27405627967661672364362767 41108441951492508546544151)
          ·
            refine ⟨61662662927238762819816227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41108441951492508546544151 61662662927238762819816227)
            ·
              refine ⟨92493994390858144229724341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61662662927238762819816227 92493994390858144229724341)
              ·
                refine ⟨8671311974142951021536657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92493994390858144229724341 8671311974142951021536657)
                ·
                  refine ⟨6503483980607213266152493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8671311974142951021536657 6503483980607213266152493)
                  ·
                    refine ⟨2438806492727704974807185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6503483980607213266152493 2438806492727704974807185)
                    ·
                      refine ⟨1829104869545778731105389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2438806492727704974807185 1829104869545778731105389)
                      ·
                        rfl

theorem cell23_3562169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5, 2, 3, 2].length) (baseStart_3562169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3562169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3562169 prefixEnd_3562169 := by exact prefixLift 3562169
  have htrace : WordTrace (prefixWord ++ tailWord_3562169) baseStart_3562169 baseEnd_3562169 := by
    simpa [prefixWord, tailWord_3562169, baseEnd_3562169] using wordTrace_append hprefix tailTrace_3562169
  have hstable : (prefixWord ++ tailWord_3562169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562169).length < 2 ^ (prefixWord ++ tailWord_3562169).sum := by decide
  have hdescent : baseEnd_3562169 < baseStart_3562169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562186 : List Nat := [3, 1, 2, 1, 4, 2, 1, 2, 2, 3, 2]
def baseStart_3562186 : Nat := 118140960795 + 3562186 * 2 ^ 59
def prefixEnd_3562186 : Nat := 4983230072969 + 3 ^ 40 * 3562186 * 2
def baseEnd_3562186 : Nat := 1829113598716905164592811

theorem tailTrace_3562186 : CollatzResearch.WordTrace tailWord_3562186 prefixEnd_3562186 1829113598716905164592811 := by
  unfold tailWord_3562186
  simp only [CollatzResearch.WordTrace]
  refine ⟨32480899268203992444716603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86615731381877313185910941 32480899268203992444716603)
  ·
    refine ⟨48721348902305988667074905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32480899268203992444716603 48721348902305988667074905)
    ·
      refine ⟨36541011676729491500306179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48721348902305988667074905 36541011676729491500306179)
      ·
        refine ⟨54811517515094237250459269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36541011676729491500306179 54811517515094237250459269)
        ·
          refine ⟨10277159534080169484461113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54811517515094237250459269 10277159534080169484461113)
          ·
            refine ⟨7707869650560127113345835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10277159534080169484461113 7707869650560127113345835)
            ·
              refine ⟨11561804475840190670018753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7707869650560127113345835 11561804475840190670018753)
              ·
                refine ⟨8671353356880143002514065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11561804475840190670018753 8671353356880143002514065)
                ·
                  refine ⟨6503515017660107251885549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8671353356880143002514065 6503515017660107251885549)
                  ·
                    refine ⟨2438818131622540219457081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6503515017660107251885549 2438818131622540219457081)
                    ·
                      refine ⟨1829113598716905164592811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2438818131622540219457081 1829113598716905164592811)
                      ·
                        rfl

theorem cell23_3562186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 2, 2, 3, 2].length) (baseStart_3562186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3562186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3562186 prefixEnd_3562186 := by exact prefixLift 3562186
  have htrace : WordTrace (prefixWord ++ tailWord_3562186) baseStart_3562186 baseEnd_3562186 := by
    simpa [prefixWord, tailWord_3562186, baseEnd_3562186] using wordTrace_append hprefix tailTrace_3562186
  have hstable : (prefixWord ++ tailWord_3562186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562186).length < 2 ^ (prefixWord ++ tailWord_3562186).sum := by decide
  have hdescent : baseEnd_3562186 < baseStart_3562186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562193 : List Nat := [1, 2, 2, 1, 2, 3, 5, 2, 1, 1, 3]
def baseStart_3562193 : Nat := 118140960795 + 3562193 * 2 ^ 59
def prefixEnd_3562193 : Nat := 4983230072969 + 3 ^ 40 * 3562193 * 2
def baseEnd_3562193 : Nat := 1829117193081486637205279

theorem tailTrace_3562193 : CollatzResearch.WordTrace tailWord_3562193 prefixEnd_3562193 1829117193081486637205279 := by
  unfold tailWord_3562193
  simp only [CollatzResearch.WordTrace]
  refine ⟨129923852383790609974371233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86615901589193739982914155 129923852383790609974371233)
  ·
    refine ⟨97442889287842957480778425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129923852383790609974371233 97442889287842957480778425)
    ·
      refine ⟨73082166965882218110583819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97442889287842957480778425 73082166965882218110583819)
      ·
        refine ⟨109623250448823327165875729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73082166965882218110583819 109623250448823327165875729)
        ·
          refine ⟨82217437836617495374406797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109623250448823327165875729 82217437836617495374406797)
          ·
            refine ⟨30831539188731560765402549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82217437836617495374406797 30831539188731560765402549)
            ·
              refine ⟨2890456798943583821756489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30831539188731560765402549 2890456798943583821756489)
              ·
                refine ⟨2167842599207687866317367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2890456798943583821756489 2167842599207687866317367)
                ·
                  refine ⟨3251763898811531799476051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2167842599207687866317367 3251763898811531799476051)
                  ·
                    refine ⟨4877645848217297699214077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3251763898811531799476051 4877645848217297699214077)
                    ·
                      refine ⟨1829117193081486637205279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4877645848217297699214077 1829117193081486637205279)
                      ·
                        rfl

theorem cell23_3562193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 2, 1, 1, 3].length) (baseStart_3562193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3562193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3562193 prefixEnd_3562193 := by exact prefixLift 3562193
  have htrace : WordTrace (prefixWord ++ tailWord_3562193) baseStart_3562193 baseEnd_3562193 := by
    simpa [prefixWord, tailWord_3562193, baseEnd_3562193] using wordTrace_append hprefix tailTrace_3562193
  have hstable : (prefixWord ++ tailWord_3562193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562193).length < 2 ^ (prefixWord ++ tailWord_3562193).sum := by decide
  have hdescent : baseEnd_3562193 < baseStart_3562193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562202 : List Nat := [3, 1, 1, 2, 2, 2, 1, 4, 1, 1, 5]
def baseStart_3562202 : Nat := 118140960795 + 3562202 * 2 ^ 59
def prefixEnd_3562202 : Nat := 4983230072969 + 3 ^ 40 * 3562202 * 2
def baseEnd_3562202 : Nat := 1829121814407377101992737

theorem tailTrace_3562202 : CollatzResearch.WordTrace tailWord_3562202 prefixEnd_3562202 1829121814407377101992737 := by
  unfold tailWord_3562202
  simp only [CollatzResearch.WordTrace]
  refine ⟨32481045160189501127862215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86616120427172003007632573 32481045160189501127862215)
  ·
    refine ⟨48721567740284251691793323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32481045160189501127862215 48721567740284251691793323)
    ·
      refine ⟨73082351610426377537689985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48721567740284251691793323 73082351610426377537689985)
      ·
        refine ⟨54811763707819783153267489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73082351610426377537689985 54811763707819783153267489)
        ·
          refine ⟨41108822780864837364950617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54811763707819783153267489 41108822780864837364950617)
          ·
            refine ⟨30831617085648628023712963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41108822780864837364950617 30831617085648628023712963)
            ·
              refine ⟨46247425628472942035569445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30831617085648628023712963 46247425628472942035569445)
              ·
                refine ⟨8671392305338676631669271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46247425628472942035569445 8671392305338676631669271)
                ·
                  refine ⟨13007088458008014947503907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8671392305338676631669271 13007088458008014947503907)
                  ·
                    refine ⟨19510632687012022421255861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13007088458008014947503907 19510632687012022421255861)
                    ·
                      refine ⟨1829121814407377101992737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19510632687012022421255861 1829121814407377101992737)
                      ·
                        rfl

theorem cell23_3562202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4, 1, 1, 5].length) (baseStart_3562202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3562202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3562202 prefixEnd_3562202 := by exact prefixLift 3562202
  have htrace : WordTrace (prefixWord ++ tailWord_3562202) baseStart_3562202 baseEnd_3562202 := by
    simpa [prefixWord, tailWord_3562202, baseEnd_3562202] using wordTrace_append hprefix tailTrace_3562202
  have hstable : (prefixWord ++ tailWord_3562202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562202).length < 2 ^ (prefixWord ++ tailWord_3562202).sum := by decide
  have hdescent : baseEnd_3562202 < baseStart_3562202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562212 : List Nat := [2, 3, 1, 1, 1, 4, 2, 1, 1, 1, 6]
def baseStart_3562212 : Nat := 118140960795 + 3562212 * 2 ^ 59
def prefixEnd_3562212 : Nat := 4983230072969 + 3 ^ 40 * 3562212 * 2
def baseEnd_3562212 : Nat := 1829126949213922062867691

theorem tailTrace_3562212 : CollatzResearch.WordTrace tailWord_3562212 prefixEnd_3562212 1829126949213922062867691 := by
  unfold tailWord_3562212
  simp only [CollatzResearch.WordTrace]
  refine ⟨64962272685360888109656445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86616363580481184146208593 64962272685360888109656445)
  ·
    refine ⟨24360852257010333041121167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64962272685360888109656445 24360852257010333041121167)
    ·
      refine ⟨36541278385515499561681751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24360852257010333041121167 36541278385515499561681751)
      ·
        refine ⟨54811917578273249342522627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36541278385515499561681751 54811917578273249342522627)
        ·
          refine ⟨82217876367409874013783941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54811917578273249342522627 82217876367409874013783941)
          ·
            refine ⟨15415851818889351377584489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82217876367409874013783941 15415851818889351377584489)
            ·
              refine ⟨11561888864167013533188367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15415851818889351377584489 11561888864167013533188367)
              ·
                refine ⟨17342833296250520299782551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11561888864167013533188367 17342833296250520299782551)
                ·
                  refine ⟨26014249944375780449673827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17342833296250520299782551 26014249944375780449673827)
                  ·
                    refine ⟨39021374916563670674510741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26014249944375780449673827 39021374916563670674510741)
                    ·
                      refine ⟨1829126949213922062867691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39021374916563670674510741 1829126949213922062867691)
                      ·
                        rfl

theorem cell23_3562212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_3562212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3562212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3562212 prefixEnd_3562212 := by exact prefixLift 3562212
  have htrace : WordTrace (prefixWord ++ tailWord_3562212) baseStart_3562212 baseEnd_3562212 := by
    simpa [prefixWord, tailWord_3562212, baseEnd_3562212] using wordTrace_append hprefix tailTrace_3562212
  have hstable : (prefixWord ++ tailWord_3562212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562212).length < 2 ^ (prefixWord ++ tailWord_3562212).sum := by decide
  have hdescent : baseEnd_3562212 < baseStart_3562212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562222 : List Nat := [4, 1, 2, 1, 1, 3, 2, 9]
def baseStart_3562222 : Nat := 118140960795 + 3562222 * 2 ^ 59
def prefixEnd_3562222 : Nat := 4983230072969 + 3 ^ 40 * 3562222 * 2
def baseEnd_3562222 : Nat := 67745632741498778657135

theorem tailTrace_3562222 : CollatzResearch.WordTrace tailWord_3562222 prefixEnd_3562222 67745632741498778657135 := by
  unfold tailWord_3562222
  simp only [CollatzResearch.WordTrace]
  refine ⟨16240613762585693490897115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86616606733790365284784613 16240613762585693490897115)
  ·
    refine ⟨24360920643878540236345673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16240613762585693490897115 24360920643878540236345673)
    ·
      refine ⟨18270690482908905177259255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24360920643878540236345673 18270690482908905177259255)
      ·
        refine ⟨27406035724363357765888883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18270690482908905177259255 27406035724363357765888883)
        ·
          refine ⟨41109053586545036648833325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27406035724363357765888883 41109053586545036648833325)
          ·
            refine ⟨15415895094954388743312497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41109053586545036648833325 15415895094954388743312497)
            ·
              refine ⟨11561921321215791557484373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15415895094954388743312497 11561921321215791557484373)
              ·
                refine ⟨67745632741498778657135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11561921321215791557484373 67745632741498778657135)
                ·
                  rfl

theorem cell23_3562222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 9].length) (baseStart_3562222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3562222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3562222 prefixEnd_3562222 := by exact prefixLift 3562222
  have htrace : WordTrace (prefixWord ++ tailWord_3562222) baseStart_3562222 baseEnd_3562222 := by
    simpa [prefixWord, tailWord_3562222, baseEnd_3562222] using wordTrace_append hprefix tailTrace_3562222
  have hstable : (prefixWord ++ tailWord_3562222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562222).length < 2 ^ (prefixWord ++ tailWord_3562222).sum := by decide
  have hdescent : baseEnd_3562222 < baseStart_3562222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562249 : List Nat := [1, 2, 1, 1, 3, 2, 2, 3, 4, 1, 3]
def baseStart_3562249 : Nat := 118140960795 + 3562249 * 2 ^ 59
def prefixEnd_3562249 : Nat := 4983230072969 + 3 ^ 40 * 3562249 * 2
def baseEnd_3562249 : Nat := 1829145947998138418105021

theorem tailTrace_3562249 : CollatzResearch.WordTrace tailWord_3562249 prefixEnd_3562249 1829145947998138418105021 := by
  unfold tailWord_3562249
  simp only [CollatzResearch.WordTrace]
  refine ⟨129925894871587731538409801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86617263247725154358939867 129925894871587731538409801)
  ·
    refine ⟨97444421153690798653807351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129925894871587731538409801 97444421153690798653807351)
    ·
      refine ⟨146166631730536197980711027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97444421153690798653807351 146166631730536197980711027)
      ·
        refine ⟨219249947595804296971066541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146166631730536197980711027 219249947595804296971066541)
        ·
          refine ⟨82218730348426611364149953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 219249947595804296971066541 82218730348426611364149953)
          ·
            refine ⟨61664047761319958523112465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82218730348426611364149953 61664047761319958523112465)
            ·
              refine ⟨46248035820989968892334349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61664047761319958523112465 46248035820989968892334349)
              ·
                refine ⟨17343013432871238334625381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46248035820989968892334349 17343013432871238334625381)
                ·
                  refine ⟨3251815018663357187742259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17343013432871238334625381 3251815018663357187742259)
                  ·
                    refine ⟨4877722527995035781613389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3251815018663357187742259 4877722527995035781613389)
                    ·
                      refine ⟨1829145947998138418105021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4877722527995035781613389 1829145947998138418105021)
                      ·
                        rfl

theorem cell23_3562249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 4, 1, 3].length) (baseStart_3562249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3562249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3562249 prefixEnd_3562249 := by exact prefixLift 3562249
  have htrace : WordTrace (prefixWord ++ tailWord_3562249) baseStart_3562249 baseEnd_3562249 := by
    simpa [prefixWord, tailWord_3562249, baseEnd_3562249] using wordTrace_append hprefix tailTrace_3562249
  have hstable : (prefixWord ++ tailWord_3562249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562249).length < 2 ^ (prefixWord ++ tailWord_3562249).sum := by decide
  have hdescent : baseEnd_3562249 < baseStart_3562249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562259 : List Nat := [1, 1, 1, 2, 1, 3, 3, 1, 5, 3, 2]
def baseStart_3562259 : Nat := 118140960795 + 3562259 * 2 ^ 59
def prefixEnd_3562259 : Nat := 4983230072969 + 3 ^ 40 * 3562259 * 2
def baseEnd_3562259 : Nat := 1829151082804683378979975

theorem tailTrace_3562259 : CollatzResearch.WordTrace tailWord_3562259 prefixEnd_3562259 1829151082804683378979975 := by
  unfold tailWord_3562259
  simp only [CollatzResearch.WordTrace]
  refine ⟨129926259601551503246273831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86617506401034335497515887 129926259601551503246273831)
  ·
    refine ⟨194889389402327254869410747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129926259601551503246273831 194889389402327254869410747)
    ·
      refine ⟨292334084103490882304116121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194889389402327254869410747 292334084103490882304116121)
      ·
        refine ⟨219250563077618161728087091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292334084103490882304116121 219250563077618161728087091)
        ·
          refine ⟨328875844616427242592130637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219250563077618161728087091 328875844616427242592130637)
          ·
            refine ⟨123328441731160215972048989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 328875844616427242592130637 123328441731160215972048989)
            ·
              refine ⟨46248165649185080989518371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123328441731160215972048989 46248165649185080989518371)
              ·
                refine ⟨69372248473777621484277557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46248165649185080989518371 69372248473777621484277557)
                ·
                  refine ⟨6503648294416652014151021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69372248473777621484277557 6503648294416652014151021)
                  ·
                    refine ⟨2438868110406244505306633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6503648294416652014151021 2438868110406244505306633)
                    ·
                      refine ⟨1829151082804683378979975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2438868110406244505306633 1829151082804683378979975)
                      ·
                        rfl

theorem cell23_3562259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 5, 3, 2].length) (baseStart_3562259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3562259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3562259 prefixEnd_3562259 := by exact prefixLift 3562259
  have htrace : WordTrace (prefixWord ++ tailWord_3562259) baseStart_3562259 baseEnd_3562259 := by
    simpa [prefixWord, tailWord_3562259, baseEnd_3562259] using wordTrace_append hprefix tailTrace_3562259
  have hstable : (prefixWord ++ tailWord_3562259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562259).length < 2 ^ (prefixWord ++ tailWord_3562259).sum := by decide
  have hdescent : baseEnd_3562259 < baseStart_3562259 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562266 : List Nat := [3, 1, 1, 3, 2, 1, 1, 5, 2, 1, 3]
def baseStart_3562266 : Nat := 118140960795 + 3562266 * 2 ^ 59
def prefixEnd_3562266 : Nat := 4983230072969 + 3 ^ 40 * 3562266 * 2
def baseEnd_3562266 : Nat := 1829154677169264851592443

theorem tailTrace_3562266 : CollatzResearch.WordTrace tailWord_3562266 prefixEnd_3562266 1829154677169264851592443 := by
  unfold tailWord_3562266
  simp only [CollatzResearch.WordTrace]
  refine ⟨32481628728131535860444663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86617676608350762294519101 32481628728131535860444663)
  ·
    refine ⟨48722443092197303790666995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32481628728131535860444663 48722443092197303790666995)
    ·
      refine ⟨73083664638295955686000493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48722443092197303790666995 73083664638295955686000493)
      ·
        refine ⟨27406374239360983382250185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73083664638295955686000493 27406374239360983382250185)
        ·
          refine ⟨20554780679520737536687639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27406374239360983382250185 20554780679520737536687639)
          ·
            refine ⟨30832171019281106305031459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20554780679520737536687639 30832171019281106305031459)
            ·
              refine ⟨46248256528921659457547189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30832171019281106305031459 46248256528921659457547189)
              ·
                refine ⟨4335774049586405574145049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46248256528921659457547189 4335774049586405574145049)
                ·
                  refine ⟨3251830537189804180608787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4335774049586405574145049 3251830537189804180608787)
                  ·
                    refine ⟨4877745805784706270913181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3251830537189804180608787 4877745805784706270913181)
                    ·
                      refine ⟨1829154677169264851592443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4877745805784706270913181 1829154677169264851592443)
                      ·
                        rfl

theorem cell23_3562266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 5, 2, 1, 3].length) (baseStart_3562266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3562266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3562266 prefixEnd_3562266 := by exact prefixLift 3562266
  have htrace : WordTrace (prefixWord ++ tailWord_3562266) baseStart_3562266 baseEnd_3562266 := by
    simpa [prefixWord, tailWord_3562266, baseEnd_3562266] using wordTrace_append hprefix tailTrace_3562266
  have hstable : (prefixWord ++ tailWord_3562266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562266).length < 2 ^ (prefixWord ++ tailWord_3562266).sum := by decide
  have hdescent : baseEnd_3562266 < baseStart_3562266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562293 : List Nat := [1, 3, 3, 1, 3, 2, 1, 3, 1, 3, 2]
def baseStart_3562293 : Nat := 118140960795 + 3562293 * 2 ^ 59
def prefixEnd_3562293 : Nat := 4983230072969 + 3 ^ 40 * 3562293 * 2
def baseEnd_3562293 : Nat := 1829168541146936245954819

theorem tailTrace_3562293 : CollatzResearch.WordTrace tailWord_3562293 prefixEnd_3562293 1829168541146936245954819 := by
  unfold tailWord_3562293
  simp only [CollatzResearch.WordTrace]
  refine ⟨129927499683428327053011533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86618333122285551368674355 129927499683428327053011533)
  ·
    refine ⟨48722812381285622644879325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129927499683428327053011533 48722812381285622644879325)
    ·
      refine ⟨18271054642982108491829747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48722812381285622644879325 18271054642982108491829747)
      ·
        refine ⟨27406581964473162737744621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18271054642982108491829747 27406581964473162737744621)
        ·
          refine ⟨10277468236677436026654233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27406581964473162737744621 10277468236677436026654233)
          ·
            refine ⟨7708101177508077019990675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10277468236677436026654233 7708101177508077019990675)
            ·
              refine ⟨11562151766262115529986013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7708101177508077019990675 11562151766262115529986013)
              ·
                refine ⟨4335806912348293323744755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11562151766262115529986013 4335806912348293323744755)
                ·
                  refine ⟨6503710368522439985617133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4335806912348293323744755 6503710368522439985617133)
                  ·
                    refine ⟨2438891388195914994606425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6503710368522439985617133 2438891388195914994606425)
                    ·
                      refine ⟨1829168541146936245954819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2438891388195914994606425 1829168541146936245954819)
                      ·
                        rfl

theorem cell23_3562293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 3, 1, 3, 2].length) (baseStart_3562293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3562293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3562293 prefixEnd_3562293 := by exact prefixLift 3562293
  have htrace : WordTrace (prefixWord ++ tailWord_3562293) baseStart_3562293 baseEnd_3562293 := by
    simpa [prefixWord, tailWord_3562293, baseEnd_3562293] using wordTrace_append hprefix tailTrace_3562293
  have hstable : (prefixWord ++ tailWord_3562293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562293).length < 2 ^ (prefixWord ++ tailWord_3562293).sum := by decide
  have hdescent : baseEnd_3562293 < baseStart_3562293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562317 : List Nat := [1, 6, 1, 2, 2, 1, 3, 1, 2, 1, 3]
def baseStart_3562317 : Nat := 118140960795 + 3562317 * 2 ^ 59
def prefixEnd_3562317 : Nat := 4983230072969 + 3 ^ 40 * 3562317 * 2
def baseEnd_3562317 : Nat := 1829180864682644152054709

theorem tailTrace_3562317 : CollatzResearch.WordTrace tailWord_3562317 prefixEnd_3562317 1829180864682644152054709 := by
  unfold tailWord_3562317
  simp only [CollatzResearch.WordTrace]
  refine ⟨129928375035341379151885205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86618916690227586101256803 129928375035341379151885205)
  ·
    refine ⟨6090392579781627147744619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 129928375035341379151885205 6090392579781627147744619)
    ·
      refine ⟨9135588869672440721616929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6090392579781627147744619 9135588869672440721616929)
      ·
        refine ⟨6851691652254330541212697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9135588869672440721616929 6851691652254330541212697)
        ·
          refine ⟨5138768739190747905909523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6851691652254330541212697 5138768739190747905909523)
          ·
            refine ⟨7708153108786121858864285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5138768739190747905909523 7708153108786121858864285)
            ·
              refine ⟨2890557415794795697074107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7708153108786121858864285 2890557415794795697074107)
              ·
                refine ⟨4335836123692193545611161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2890557415794795697074107 4335836123692193545611161)
                ·
                  refine ⟨3251877092769145159208371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4335836123692193545611161 3251877092769145159208371)
                  ·
                    refine ⟨4877815639153717738812557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3251877092769145159208371 4877815639153717738812557)
                    ·
                      refine ⟨1829180864682644152054709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4877815639153717738812557 1829180864682644152054709)
                      ·
                        rfl

theorem cell23_3562317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_3562317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3562317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3562317 prefixEnd_3562317 := by exact prefixLift 3562317
  have htrace : WordTrace (prefixWord ++ tailWord_3562317) baseStart_3562317 baseEnd_3562317 := by
    simpa [prefixWord, tailWord_3562317, baseEnd_3562317] using wordTrace_append hprefix tailTrace_3562317
  have hstable : (prefixWord ++ tailWord_3562317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562317).length < 2 ^ (prefixWord ++ tailWord_3562317).sum := by decide
  have hdescent : baseEnd_3562317 < baseStart_3562317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562449 : List Nat := [1, 2, 2, 1, 2, 1, 3, 3, 3, 5]
def baseStart_3562449 : Nat := 118140960795 + 3562449 * 2 ^ 59
def prefixEnd_3562449 : Nat := 4983230072969 + 3 ^ 40 * 3562449 * 2
def baseEnd_3562449 : Nat := 609749548043012545201367

theorem tailTrace_3562449 : CollatzResearch.WordTrace tailWord_3562449 prefixEnd_3562449 609749548043012545201367 := by
  unfold tailWord_3562449
  simp only [CollatzResearch.WordTrace]
  refine ⟨129933189470863165695690401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86622126313908777130460267 129933189470863165695690401)
  ·
    refine ⟨97449892103147374271767801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129933189470863165695690401 97449892103147374271767801)
    ·
      refine ⟨73087419077360530703825851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97449892103147374271767801 73087419077360530703825851)
      ·
        refine ⟨109631128616040796055738777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73087419077360530703825851 109631128616040796055738777)
        ·
          refine ⟨82223346462030597041804083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109631128616040796055738777 82223346462030597041804083)
          ·
            refine ⟨123335019693045895562706125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82223346462030597041804083 123335019693045895562706125)
            ·
              refine ⟨46250632384892210836014797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123335019693045895562706125 46250632384892210836014797)
              ·
                refine ⟨17343987144334579063505549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46250632384892210836014797 17343987144334579063505549)
                ·
                  refine ⟨6503995179125467148814581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17343987144334579063505549 6503995179125467148814581)
                  ·
                    refine ⟨609749548043012545201367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6503995179125467148814581 609749548043012545201367)
                    ·
                      rfl

theorem cell23_3562449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 3, 5].length) (baseStart_3562449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3562449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3562449 prefixEnd_3562449 := by exact prefixLift 3562449
  have htrace : WordTrace (prefixWord ++ tailWord_3562449) baseStart_3562449 baseEnd_3562449 := by
    simpa [prefixWord, tailWord_3562449, baseEnd_3562449] using wordTrace_append hprefix tailTrace_3562449
  have hstable : (prefixWord ++ tailWord_3562449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562449).length < 2 ^ (prefixWord ++ tailWord_3562449).sum := by decide
  have hdescent : baseEnd_3562449 < baseStart_3562449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562450 : List Nat := [3, 2, 2, 3, 1, 3, 1, 1, 2, 2, 3]
def baseStart_3562450 : Nat := 118140960795 + 3562450 * 2 ^ 59
def prefixEnd_3562450 : Nat := 4983230072969 + 3 ^ 40 * 3562450 * 2
def baseEnd_3562450 : Nat := 1829249157609692131691597

theorem tailTrace_3562450 : CollatzResearch.WordTrace tailWord_3562450 prefixEnd_3562450 1829249157609692131691597 := by
  unfold tailWord_3562450
  simp only [CollatzResearch.WordTrace]
  refine ⟨32483306485964885716619201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86622150629239695244317869 32483306485964885716619201)
  ·
    refine ⟨24362479864473664287464401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32483306485964885716619201 24362479864473664287464401)
    ·
      refine ⟨18271859898355248215598301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24362479864473664287464401 18271859898355248215598301)
      ·
        refine ⟨6851947461883218080849363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18271859898355248215598301 6851947461883218080849363)
        ·
          refine ⟨10277921192824827121274045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6851947461883218080849363 10277921192824827121274045)
          ·
            refine ⟨3854220447309310170477767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10277921192824827121274045 3854220447309310170477767)
            ·
              refine ⟨5781330670963965255716651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3854220447309310170477767 5781330670963965255716651)
              ·
                refine ⟨8671996006445947883574977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5781330670963965255716651 8671996006445947883574977)
                ·
                  refine ⟨6503997004834460912681233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8671996006445947883574977 6503997004834460912681233)
                  ·
                    refine ⟨4877997753625845684510925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6503997004834460912681233 4877997753625845684510925)
                    ·
                      refine ⟨1829249157609692131691597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4877997753625845684510925 1829249157609692131691597)
                      ·
                        rfl

theorem cell23_3562450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_3562450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3562450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3562450 prefixEnd_3562450 := by exact prefixLift 3562450
  have htrace : WordTrace (prefixWord ++ tailWord_3562450) baseStart_3562450 baseEnd_3562450 := by
    simpa [prefixWord, tailWord_3562450, baseEnd_3562450] using wordTrace_append hprefix tailTrace_3562450
  have hstable : (prefixWord ++ tailWord_3562450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562450).length < 2 ^ (prefixWord ++ tailWord_3562450).sum := by decide
  have hdescent : baseEnd_3562450 < baseStart_3562450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562503 : List Nat := [1, 1, 4, 3, 1, 1, 4, 2, 1, 1, 4]
def baseStart_3562503 : Nat := 118140960795 + 3562503 * 2 ^ 59
def prefixEnd_3562503 : Nat := 4983230072969 + 3 ^ 40 * 3562503 * 2
def baseEnd_3562503 : Nat := 1829276372084380424328853

theorem tailTrace_3562503 : CollatzResearch.WordTrace tailWord_3562503 prefixEnd_3562503 1829276372084380424328853 := by
  unfold tailWord_3562503
  simp only [CollatzResearch.WordTrace]
  refine ⟨129935159012667532918156163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86623439341778355278770775 129935159012667532918156163)
  ·
    refine ⟨194902738519001299377234245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129935159012667532918156163 194902738519001299377234245)
    ·
      refine ⟨36544263472312743633231421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194902738519001299377234245 36544263472312743633231421)
      ·
        refine ⟨13704098802117278862461783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36544263472312743633231421 13704098802117278862461783)
        ·
          refine ⟨20556148203175918293692675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13704098802117278862461783 20556148203175918293692675)
          ·
            refine ⟨30834222304763877440539013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20556148203175918293692675 30834222304763877440539013)
            ·
              refine ⟨5781416682143227020101065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30834222304763877440539013 5781416682143227020101065)
              ·
                refine ⟨4336062511607420265075799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5781416682143227020101065 4336062511607420265075799)
                ·
                  refine ⟨6504093767411130397613699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4336062511607420265075799 6504093767411130397613699)
                  ·
                    refine ⟨9756140651116695596420549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6504093767411130397613699 9756140651116695596420549)
                    ·
                      refine ⟨1829276372084380424328853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9756140651116695596420549 1829276372084380424328853)
                      ·
                        rfl

theorem cell23_3562503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_3562503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3562503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3562503 prefixEnd_3562503 := by exact prefixLift 3562503
  have htrace : WordTrace (prefixWord ++ tailWord_3562503) baseStart_3562503 baseEnd_3562503 := by
    simpa [prefixWord, tailWord_3562503, baseEnd_3562503] using wordTrace_append hprefix tailTrace_3562503
  have hstable : (prefixWord ++ tailWord_3562503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562503).length < 2 ^ (prefixWord ++ tailWord_3562503).sum := by decide
  have hdescent : baseEnd_3562503 < baseStart_3562503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562539 : List Nat := [1, 1, 1, 1, 2, 1, 6, 1, 2, 7]
def baseStart_3562539 : Nat := 118140960795 + 3562539 * 2 ^ 59
def prefixEnd_3562539 : Nat := 4983230072969 + 3 ^ 40 * 3562539 * 2
def baseEnd_3562539 : Nat := 609764952462647427826229

theorem tailTrace_3562539 : CollatzResearch.WordTrace tailWord_3562539 prefixEnd_3562539 609764952462647427826229 := by
  unfold tailWord_3562539
  simp only [CollatzResearch.WordTrace]
  refine ⟨129936472040537111066466671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86624314693691407377644447 129936472040537111066466671)
  ·
    refine ⟨194904708060805666599700007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129936472040537111066466671 194904708060805666599700007)
    ·
      refine ⟨292357062091208499899550011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194904708060805666599700007 292357062091208499899550011)
      ·
        refine ⟨438535593136812749849325017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292357062091208499899550011 438535593136812749849325017)
        ·
          refine ⟨328901694852609562386993763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 438535593136812749849325017 328901694852609562386993763)
          ·
            refine ⟨493352542278914343580490645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328901694852609562386993763 493352542278914343580490645)
            ·
              refine ⟨23125900419324109855335499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 493352542278914343580490645 23125900419324109855335499)
              ·
                refine ⟨34688850628986164783003249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23125900419324109855335499 34688850628986164783003249)
                ·
                  refine ⟨26016637971739623587252437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34688850628986164783003249 26016637971739623587252437)
                  ·
                    refine ⟨609764952462647427826229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26016637971739623587252437 609764952462647427826229)
                    ·
                      rfl

theorem cell23_3562539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 7].length) (baseStart_3562539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3562539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3562539 prefixEnd_3562539 := by exact prefixLift 3562539
  have htrace : WordTrace (prefixWord ++ tailWord_3562539) baseStart_3562539 baseEnd_3562539 := by
    simpa [prefixWord, tailWord_3562539, baseEnd_3562539] using wordTrace_append hprefix tailTrace_3562539
  have hstable : (prefixWord ++ tailWord_3562539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562539).length < 2 ^ (prefixWord ++ tailWord_3562539).sum := by decide
  have hdescent : baseEnd_3562539 < baseStart_3562539 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562559 : List Nat := [1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 8]
def baseStart_3562559 : Nat := 118140960795 + 3562559 * 2 ^ 59
def prefixEnd_3562559 : Nat := 4983230072969 + 3 ^ 40 * 3562559 * 2
def baseEnd_3562559 : Nat := 1829305127001032205228595

theorem tailTrace_3562559 : CollatzResearch.WordTrace tailWord_3562559 prefixEnd_3562559 1829305127001032205228595 := by
  unfold tailWord_3562559
  simp only [CollatzResearch.WordTrace]
  refine ⟨129937201500464654482194731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86624801000309769654796487 129937201500464654482194731)
  ·
    refine ⟨194905802250696981723292097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129937201500464654482194731 194905802250696981723292097)
    ·
      refine ⟨146179351688022736292469073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194905802250696981723292097 146179351688022736292469073)
      ·
        refine ⟨109634513766017052219351805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146179351688022736292469073 109634513766017052219351805)
        ·
          refine ⟨41112942662256394582256927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109634513766017052219351805 41112942662256394582256927)
          ·
            refine ⟨61669413993384591873385391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41112942662256394582256927 61669413993384591873385391)
            ·
              refine ⟨92504120990076887810078087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61669413993384591873385391 92504120990076887810078087)
              ·
                refine ⟨138756181485115331715117131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92504120990076887810078087 138756181485115331715117131)
                ·
                  refine ⟨208134272227672997572675697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138756181485115331715117131 208134272227672997572675697)
                  ·
                    refine ⟨156100704170754748179506773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 208134272227672997572675697 156100704170754748179506773)
                    ·
                      refine ⟨1829305127001032205228595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 156100704170754748179506773 1829305127001032205228595)
                      ·
                        rfl

theorem cell23_3562559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 8].length) (baseStart_3562559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3562559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3562559 prefixEnd_3562559 := by exact prefixLift 3562559
  have htrace : WordTrace (prefixWord ++ tailWord_3562559) baseStart_3562559 baseEnd_3562559 := by
    simpa [prefixWord, tailWord_3562559, baseEnd_3562559] using wordTrace_append hprefix tailTrace_3562559
  have hstable : (prefixWord ++ tailWord_3562559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562559).length < 2 ^ (prefixWord ++ tailWord_3562559).sum := by decide
  have hdescent : baseEnd_3562559 < baseStart_3562559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562563 : List Nat := [1, 1, 1, 3, 1, 2, 5, 1, 3, 3, 2]
def baseStart_3562563 : Nat := 118140960795 + 3562563 * 2 ^ 59
def prefixEnd_3562563 : Nat := 4983230072969 + 3 ^ 40 * 3562563 * 2
def baseEnd_3562563 : Nat := 1829307180923650189578577

theorem tailTrace_3562563 : CollatzResearch.WordTrace tailWord_3562563 prefixEnd_3562563 1829307180923650189578577 := by
  unfold tailWord_3562563
  simp only [CollatzResearch.WordTrace]
  refine ⟨129937347392450163165340343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86624898261633442110226895 129937347392450163165340343)
  ·
    refine ⟨194906021088675244748010515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129937347392450163165340343 194906021088675244748010515)
    ·
      refine ⟨292359031633012867122015773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194906021088675244748010515 292359031633012867122015773)
      ·
        refine ⟨109634636862379825170755915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 292359031633012867122015773 109634636862379825170755915)
        ·
          refine ⟨164451955293569737756133873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109634636862379825170755915 164451955293569737756133873)
          ·
            refine ⟨123338966470177303317100405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164451955293569737756133873 123338966470177303317100405)
            ·
              refine ⟨11563028106579122185978163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 123338966470177303317100405 11563028106579122185978163)
              ·
                refine ⟨17344542159868683278967245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11563028106579122185978163 17344542159868683278967245)
                ·
                  refine ⟨6504203309950756229612717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17344542159868683278967245 6504203309950756229612717)
                  ·
                    refine ⟨2439076241231533586104769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6504203309950756229612717 2439076241231533586104769)
                    ·
                      refine ⟨1829307180923650189578577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2439076241231533586104769 1829307180923650189578577)
                      ·
                        rfl

theorem cell23_3562563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 3, 3, 2].length) (baseStart_3562563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3562563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3562563 prefixEnd_3562563 := by exact prefixLift 3562563
  have htrace : WordTrace (prefixWord ++ tailWord_3562563) baseStart_3562563 baseEnd_3562563 := by
    simpa [prefixWord, tailWord_3562563, baseEnd_3562563] using wordTrace_append hprefix tailTrace_3562563
  have hstable : (prefixWord ++ tailWord_3562563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562563).length < 2 ^ (prefixWord ++ tailWord_3562563).sum := by decide
  have hdescent : baseEnd_3562563 < baseStart_3562563 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562569 : List Nat := [1, 2, 1, 1, 2, 2, 2, 1, 3, 8]
def baseStart_3562569 : Nat := 118140960795 + 3562569 * 2 ^ 59
def prefixEnd_3562569 : Nat := 4983230072969 + 3 ^ 40 * 3562569 * 2
def baseEnd_3562569 : Nat := 609770087269192388701183

theorem tailTrace_3562569 : CollatzResearch.WordTrace tailWord_3562569 prefixEnd_3562569 609770087269192388701183 := by
  unfold tailWord_3562569
  simp only [CollatzResearch.WordTrace]
  refine ⟨129937566230428426190058761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86625044153618950793372507 129937566230428426190058761)
  ·
    refine ⟨97453174672821319642544071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129937566230428426190058761 97453174672821319642544071)
    ·
      refine ⟨146179762009231979463816107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97453174672821319642544071 146179762009231979463816107)
      ·
        refine ⟨219269643013847969195724161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146179762009231979463816107 219269643013847969195724161)
        ·
          refine ⟨164452232260385976896793121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219269643013847969195724161 164452232260385976896793121)
          ·
            refine ⟨123339174195289482672594841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164452232260385976896793121 123339174195289482672594841)
            ·
              refine ⟨92504380646467112004446131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123339174195289482672594841 92504380646467112004446131)
              ·
                refine ⟨138756570969700668006669197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92504380646467112004446131 138756570969700668006669197)
                ·
                  refine ⟨52033714113637750502500949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138756570969700668006669197 52033714113637750502500949)
                  ·
                    refine ⟨609770087269192388701183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 52033714113637750502500949 609770087269192388701183)
                    ·
                      rfl

theorem cell23_3562569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 8].length) (baseStart_3562569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3562569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3562569 prefixEnd_3562569 := by exact prefixLift 3562569
  have htrace : WordTrace (prefixWord ++ tailWord_3562569) baseStart_3562569 baseEnd_3562569 := by
    simpa [prefixWord, tailWord_3562569, baseEnd_3562569] using wordTrace_append hprefix tailTrace_3562569
  have hstable : (prefixWord ++ tailWord_3562569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562569).length < 2 ^ (prefixWord ++ tailWord_3562569).sum := by decide
  have hdescent : baseEnd_3562569 < baseStart_3562569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562580 : List Nat := [2, 4, 1, 1, 1, 1, 2, 5, 1, 3, 2]
def baseStart_3562580 : Nat := 118140960795 + 3562580 * 2 ^ 59
def prefixEnd_3562580 : Nat := 4983230072969 + 3 ^ 40 * 3562580 * 2
def baseEnd_3562580 : Nat := 1829315910094776623065999

theorem tailTrace_3562580 : CollatzResearch.WordTrace tailWord_3562580 prefixEnd_3562580 1829315910094776623065999 := by
  unfold tailWord_3562580
  simp only [CollatzResearch.WordTrace]
  refine ⟨64968983716694287534354597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86625311622259050045806129 64968983716694287534354597)
  ·
    refine ⟨12181684446880178912691487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64968983716694287534354597 12181684446880178912691487)
    ·
      refine ⟨18272526670320268369037231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12181684446880178912691487 18272526670320268369037231)
      ·
        refine ⟨27408790005480402553555847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18272526670320268369037231 27408790005480402553555847)
        ·
          refine ⟨41113185008220603830333771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27408790005480402553555847 41113185008220603830333771)
          ·
            refine ⟨61669777512330905745500657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41113185008220603830333771 61669777512330905745500657)
            ·
              refine ⟨46252333134248179309125493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61669777512330905745500657 46252333134248179309125493)
              ·
                refine ⟨4336156231335766810230515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46252333134248179309125493 4336156231335766810230515)
                ·
                  refine ⟨6504234347003650215345773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4336156231335766810230515 6504234347003650215345773)
                  ·
                    refine ⟨2439087880126368830754665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6504234347003650215345773 2439087880126368830754665)
                    ·
                      refine ⟨1829315910094776623065999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2439087880126368830754665 1829315910094776623065999)
                      ·
                        rfl

theorem cell23_3562580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 5, 1, 3, 2].length) (baseStart_3562580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3562580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3562580 prefixEnd_3562580 := by exact prefixLift 3562580
  have htrace : WordTrace (prefixWord ++ tailWord_3562580) baseStart_3562580 baseEnd_3562580 := by
    simpa [prefixWord, tailWord_3562580, baseEnd_3562580] using wordTrace_append hprefix tailTrace_3562580
  have hstable : (prefixWord ++ tailWord_3562580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562580).length < 2 ^ (prefixWord ++ tailWord_3562580).sum := by decide
  have hdescent : baseEnd_3562580 < baseStart_3562580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562590 : List Nat := [4, 4, 1, 1, 1, 1, 1, 1, 2, 7]
def baseStart_3562590 : Nat := 118140960795 + 3562590 * 2 ^ 59
def prefixEnd_3562590 : Nat := 4983230072969 + 3 ^ 40 * 3562590 * 2
def baseEnd_3562590 : Nat := 609773681633773861313651

theorem tailTrace_3562590 : CollatzResearch.WordTrace tailWord_3562590 prefixEnd_3562590 609773681633773861313651 := by
  unfold tailWord_3562590
  simp only [CollatzResearch.WordTrace]
  refine ⟨16242291520419043347071653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86625554775568231184382149 16242291520419043347071653)
  ·
    refine ⟨3045429660078570627575935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16242291520419043347071653 3045429660078570627575935)
    ·
      refine ⟨4568144490117855941363903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3045429660078570627575935 4568144490117855941363903)
      ·
        refine ⟨6852216735176783912045855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4568144490117855941363903 6852216735176783912045855)
        ·
          refine ⟨10278325102765175868068783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6852216735176783912045855 10278325102765175868068783)
          ·
            refine ⟨15417487654147763802103175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10278325102765175868068783 15417487654147763802103175)
            ·
              refine ⟨23126231481221645703154763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15417487654147763802103175 23126231481221645703154763)
              ·
                refine ⟨34689347221832468554732145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23126231481221645703154763 34689347221832468554732145)
                ·
                  refine ⟨26017010416374351416049109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34689347221832468554732145 26017010416374351416049109)
                  ·
                    refine ⟨609773681633773861313651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26017010416374351416049109 609773681633773861313651)
                    ·
                      rfl

theorem cell23_3562590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_3562590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3562590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3562590 prefixEnd_3562590 := by exact prefixLift 3562590
  have htrace : WordTrace (prefixWord ++ tailWord_3562590) baseStart_3562590 baseEnd_3562590 := by
    simpa [prefixWord, tailWord_3562590, baseEnd_3562590] using wordTrace_append hprefix tailTrace_3562590
  have hstable : (prefixWord ++ tailWord_3562590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562590).length < 2 ^ (prefixWord ++ tailWord_3562590).sum := by decide
  have hdescent : baseEnd_3562590 < baseStart_3562590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562610 : List Nat := [3, 2, 1, 2, 2, 1, 4, 1, 1, 4, 2]
def baseStart_3562610 : Nat := 118140960795 + 3562610 * 2 ^ 59
def prefixEnd_3562610 : Nat := 4983230072969 + 3 ^ 40 * 3562610 * 2
def baseEnd_3562610 : Nat := 1829331314514411505690861

theorem tailTrace_3562610 : CollatzResearch.WordTrace tailWord_3562610 prefixEnd_3562610 1829331314514411505690861 := by
  unfold tailWord_3562610
  simp only [CollatzResearch.WordTrace]
  refine ⟨32484765405819972548075321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86626041082186593461534189 32484765405819972548075321)
  ·
    refine ⟨24363574054364979411056491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32484765405819972548075321 24363574054364979411056491)
    ·
      refine ⟨36545361081547469116584737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24363574054364979411056491 36545361081547469116584737)
      ·
        refine ⟨27409020811160601837438553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36545361081547469116584737 27409020811160601837438553)
        ·
          refine ⟨20556765608370451378078915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27409020811160601837438553 20556765608370451378078915)
          ·
            refine ⟨30835148412555677067118373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20556765608370451378078915 30835148412555677067118373)
            ·
              refine ⟨5781590327354189450084695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30835148412555677067118373 5781590327354189450084695)
              ·
                refine ⟨8672385491031284175127043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5781590327354189450084695 8672385491031284175127043)
                ·
                  refine ⟨13008578236546926262690565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8672385491031284175127043 13008578236546926262690565)
                  ·
                    refine ⟨2439108419352548674254481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13008578236546926262690565 2439108419352548674254481)
                    ·
                      refine ⟨1829331314514411505690861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2439108419352548674254481 1829331314514411505690861)
                      ·
                        rfl

theorem cell23_3562610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 1, 1, 4, 2].length) (baseStart_3562610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3562610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3562610 prefixEnd_3562610 := by exact prefixLift 3562610
  have htrace : WordTrace (prefixWord ++ tailWord_3562610) baseStart_3562610 baseEnd_3562610 := by
    simpa [prefixWord, tailWord_3562610, baseEnd_3562610] using wordTrace_append hprefix tailTrace_3562610
  have hstable : (prefixWord ++ tailWord_3562610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562610).length < 2 ^ (prefixWord ++ tailWord_3562610).sum := by decide
  have hdescent : baseEnd_3562610 < baseStart_3562610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562633 : List Nat := [1, 2, 1, 1, 4, 3, 1, 5, 5]
def baseStart_3562633 : Nat := 118140960795 + 3562633 * 2 ^ 59
def prefixEnd_3562633 : Nat := 4983230072969 + 3 ^ 40 * 3562633 * 2
def baseEnd_3562633 : Nat := 203260347174384990633695

theorem tailTrace_3562633 : CollatzResearch.WordTrace tailWord_3562633 prefixEnd_3562633 203260347174384990633695 := by
  unfold tailWord_3562633
  simp only [CollatzResearch.WordTrace]
  refine ⟨129939900502196565120388553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86626600334797710080259035 129939900502196565120388553)
  ·
    refine ⟨97454925376647423840291415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129939900502196565120388553 97454925376647423840291415)
    ·
      refine ⟨146182388064971135760437123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97454925376647423840291415 146182388064971135760437123)
      ·
        refine ⟨219273582097456703640655685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146182388064971135760437123 219273582097456703640655685)
        ·
          refine ⟨41113796643273131932622941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 219273582097456703640655685 41113796643273131932622941)
          ·
            refine ⟨15417673741227424474733603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41113796643273131932622941 15417673741227424474733603)
            ·
              refine ⟨23126510611841136712100405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15417673741227424474733603 23126510611841136712100405)
              ·
                refine ⟨2168110369860106566759413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23126510611841136712100405 2168110369860106566759413)
                ·
                  refine ⟨203260347174384990633695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2168110369860106566759413 203260347174384990633695)
                  ·
                    rfl

theorem cell23_3562633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 5, 5].length) (baseStart_3562633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3562633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3562633 prefixEnd_3562633 := by exact prefixLift 3562633
  have htrace : WordTrace (prefixWord ++ tailWord_3562633) baseStart_3562633 baseEnd_3562633 := by
    simpa [prefixWord, tailWord_3562633, baseEnd_3562633] using wordTrace_append hprefix tailTrace_3562633
  have hstable : (prefixWord ++ tailWord_3562633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562633).length < 2 ^ (prefixWord ++ tailWord_3562633).sum := by decide
  have hdescent : baseEnd_3562633 < baseStart_3562633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562650 : List Nat := [3, 1, 1, 5, 1, 1, 2, 4, 5]
def baseStart_3562650 : Nat := 118140960795 + 3562650 * 2 ^ 59
def prefixEnd_3562650 : Nat := 4983230072969 + 3 ^ 40 * 3562650 * 2
def baseEnd_3562650 : Nat := 203261317082287927687853

theorem tailTrace_3562650 : CollatzResearch.WordTrace tailWord_3562650 prefixEnd_3562650 203261317082287927687853 := by
  unfold tailWord_3562650
  simp only [CollatzResearch.WordTrace]
  refine ⟨32485130135783744255939351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86627013695423318015838269 32485130135783744255939351)
  ·
    refine ⟨48727695203675616383909027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32485130135783744255939351 48727695203675616383909027)
    ·
      refine ⟨73091542805513424575863541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48727695203675616383909027 73091542805513424575863541)
      ·
        refine ⟨6852332138016883553987207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73091542805513424575863541 6852332138016883553987207)
        ·
          refine ⟨10278498207025325330980811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6852332138016883553987207 10278498207025325330980811)
          ·
            refine ⟨15417747310537987996471217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10278498207025325330980811 15417747310537987996471217)
            ·
              refine ⟨11563310482903490997353413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15417747310537987996471217 11563310482903490997353413)
              ·
                refine ⟨2168120715544404562003765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11563310482903490997353413 2168120715544404562003765)
                ·
                  refine ⟨203261317082287927687853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2168120715544404562003765 203261317082287927687853)
                  ·
                    rfl

theorem cell23_3562650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 4, 5].length) (baseStart_3562650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3562650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3562650 prefixEnd_3562650 := by exact prefixLift 3562650
  have htrace : WordTrace (prefixWord ++ tailWord_3562650) baseStart_3562650 baseEnd_3562650 := by
    simpa [prefixWord, tailWord_3562650, baseEnd_3562650] using wordTrace_append hprefix tailTrace_3562650
  have hstable : (prefixWord ++ tailWord_3562650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562650).length < 2 ^ (prefixWord ++ tailWord_3562650).sum := by decide
  have hdescent : baseEnd_3562650 < baseStart_3562650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562656 : List Nat := [2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 7]
def baseStart_3562656 : Nat := 118140960795 + 3562656 * 2 ^ 59
def prefixEnd_3562656 : Nat := 4983230072969 + 3 ^ 40 * 3562656 * 2
def baseEnd_3562656 : Nat := 1829354934624518325715649

theorem tailTrace_3562656 : CollatzResearch.WordTrace tailWord_3562656 prefixEnd_3562656 1829354934624518325715649 := by
  unfold tailWord_3562656
  simp only [CollatzResearch.WordTrace]
  refine ⟨64970369690556620024237911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86627159587408826698983881 64970369690556620024237911)
  ·
    refine ⟨97455554535834930036356867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64970369690556620024237911 97455554535834930036356867)
    ·
      refine ⟨146183331803752395054535301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97455554535834930036356867 146183331803752395054535301)
      ·
        refine ⟨27409374713203574072725369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146183331803752395054535301 27409374713203574072725369)
        ·
          refine ⟨20557031034902680554544027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27409374713203574072725369 20557031034902680554544027)
          ·
            refine ⟨30835546552354020831816041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20557031034902680554544027 30835546552354020831816041)
            ·
              refine ⟨23126659914265515623862031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30835546552354020831816041 23126659914265515623862031)
              ·
                refine ⟨34689989871398273435793047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23126659914265515623862031 34689989871398273435793047)
                ·
                  refine ⟨52034984807097410153689571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34689989871398273435793047 52034984807097410153689571)
                  ·
                    refine ⟨78052477210646115230534357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52034984807097410153689571 78052477210646115230534357)
                    ·
                      refine ⟨1829354934624518325715649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 78052477210646115230534357 1829354934624518325715649)
                      ·
                        rfl

theorem cell23_3562656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_3562656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3562656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3562656 prefixEnd_3562656 := by exact prefixLift 3562656
  have htrace : WordTrace (prefixWord ++ tailWord_3562656) baseStart_3562656 baseEnd_3562656 := by
    simpa [prefixWord, tailWord_3562656, baseEnd_3562656] using wordTrace_append hprefix tailTrace_3562656
  have hstable : (prefixWord ++ tailWord_3562656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562656).length < 2 ^ (prefixWord ++ tailWord_3562656).sum := by decide
  have hdescent : baseEnd_3562656 < baseStart_3562656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562663 : List Nat := [1, 1, 6, 2, 1, 1, 1, 2, 1, 7]
def baseStart_3562663 : Nat := 118140960795 + 3562663 * 2 ^ 59
def prefixEnd_3562663 : Nat := 4983230072969 + 3 ^ 40 * 3562663 * 2
def baseEnd_3562663 : Nat := 609786176329699932776039

theorem tailTrace_3562663 : CollatzResearch.WordTrace tailWord_3562663 prefixEnd_3562663 609786176329699932776039 := by
  unfold tailWord_3562663
  simp only [CollatzResearch.WordTrace]
  refine ⟨129940994692087880243980643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86627329794725253495987095 129940994692087880243980643)
  ·
    refine ⟨194911492038131820365970965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129940994692087880243980643 194911492038131820365970965)
    ·
      refine ⟨9136476189287429079654889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 194911492038131820365970965 9136476189287429079654889)
      ·
        refine ⟨6852357141965571809741167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9136476189287429079654889 6852357141965571809741167)
        ·
          refine ⟨10278535712948357714611751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6852357141965571809741167 10278535712948357714611751)
          ·
            refine ⟨15417803569422536571917627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10278535712948357714611751 15417803569422536571917627)
            ·
              refine ⟨23126705354133804857876441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15417803569422536571917627 23126705354133804857876441)
              ·
                refine ⟨17345029015600353643407331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23126705354133804857876441 17345029015600353643407331)
                ·
                  refine ⟨26017543523400530465110997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17345029015600353643407331 26017543523400530465110997)
                  ·
                    refine ⟨609786176329699932776039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26017543523400530465110997 609786176329699932776039)
                    ·
                      rfl

theorem cell23_3562663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_3562663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3562663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3562663 prefixEnd_3562663 := by exact prefixLift 3562663
  have htrace : WordTrace (prefixWord ++ tailWord_3562663) baseStart_3562663 baseEnd_3562663 := by
    simpa [prefixWord, tailWord_3562663, baseEnd_3562663] using wordTrace_append hprefix tailTrace_3562663
  have hstable : (prefixWord ++ tailWord_3562663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562663).length < 2 ^ (prefixWord ++ tailWord_3562663).sum := by decide
  have hdescent : baseEnd_3562663 < baseStart_3562663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562683 : List Nat := [1, 1, 1, 1, 1, 2, 4, 2, 4, 4, 2]
def baseStart_3562683 : Nat := 118140960795 + 3562683 * 2 ^ 59
def prefixEnd_3562683 : Nat := 4983230072969 + 3 ^ 40 * 3562683 * 2
def baseEnd_3562683 : Nat := 1829368798602189720078025

theorem tailTrace_3562683 : CollatzResearch.WordTrace tailWord_3562683 prefixEnd_3562683 1829368798602189720078025 := by
  unfold tailWord_3562683
  simp only [CollatzResearch.WordTrace]
  refine ⟨129941724152015423659708703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86627816101343615773139135 129941724152015423659708703)
  ·
    refine ⟨194912586228023135489563055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129941724152015423659708703 194912586228023135489563055)
    ·
      refine ⟨292368879342034703234344583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194912586228023135489563055 292368879342034703234344583)
      ·
        refine ⟨438553319013052054851516875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292368879342034703234344583 438553319013052054851516875)
        ·
          refine ⟨657829978519578082277275313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 438553319013052054851516875 657829978519578082277275313)
          ·
            refine ⟨493372483889683561707956485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 657829978519578082277275313 493372483889683561707956485)
            ·
              refine ⟨92507340729315667820241841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 493372483889683561707956485 92507340729315667820241841)
              ·
                refine ⟨69380505546986750865181381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92507340729315667820241841 69380505546986750865181381)
                ·
                  refine ⟨13008844790060015787221509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69380505546986750865181381 13008844790060015787221509)
                  ·
                    refine ⟨2439158398136252960104033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13008844790060015787221509 2439158398136252960104033)
                    ·
                      refine ⟨1829368798602189720078025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2439158398136252960104033 1829368798602189720078025)
                      ·
                        rfl

theorem cell23_3562683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4, 4, 2].length) (baseStart_3562683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3562683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3562683 prefixEnd_3562683 := by exact prefixLift 3562683
  have htrace : WordTrace (prefixWord ++ tailWord_3562683) baseStart_3562683 baseEnd_3562683 := by
    simpa [prefixWord, tailWord_3562683, baseEnd_3562683] using wordTrace_append hprefix tailTrace_3562683
  have hstable : (prefixWord ++ tailWord_3562683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562683).length < 2 ^ (prefixWord ++ tailWord_3562683).sum := by decide
  have hdescent : baseEnd_3562683 < baseStart_3562683 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562696 : List Nat := [2, 1, 3, 1, 2, 1, 2, 1, 1, 3, 6]
def baseStart_3562696 : Nat := 118140960795 + 3562696 * 2 ^ 59
def prefixEnd_3562696 : Nat := 4983230072969 + 3 ^ 40 * 3562696 * 2
def baseEnd_3562696 : Nat := 1829375473850698169215465

theorem tailTrace_3562696 : CollatzResearch.WordTrace tailWord_3562696 prefixEnd_3562696 1829375473850698169215465 := by
  unfold tailWord_3562696
  simp only [CollatzResearch.WordTrace]
  refine ⟨64971099150484163439965971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86628132200645551253287961 64971099150484163439965971)
  ·
    refine ⟨97456648725726245159948957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64971099150484163439965971 97456648725726245159948957)
    ·
      refine ⟨36546243272147341934980859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97456648725726245159948957 36546243272147341934980859)
      ·
        refine ⟨54819364908221012902471289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36546243272147341934980859 54819364908221012902471289)
        ·
          refine ⟨41114523681165759676853467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54819364908221012902471289 41114523681165759676853467)
          ·
            refine ⟨61671785521748639515280201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41114523681165759676853467 61671785521748639515280201)
            ·
              refine ⟨46253839141311479636460151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61671785521748639515280201 46253839141311479636460151)
              ·
                refine ⟨69380758711967219454690227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46253839141311479636460151 69380758711967219454690227)
                ·
                  refine ⟨104071138067950829182035341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69380758711967219454690227 104071138067950829182035341)
                  ·
                    refine ⟨39026676775481560943263253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 104071138067950829182035341 39026676775481560943263253)
                    ·
                      refine ⟨1829375473850698169215465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39026676775481560943263253 1829375473850698169215465)
                      ·
                        rfl

theorem cell23_3562696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_3562696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3562696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3562696 prefixEnd_3562696 := by exact prefixLift 3562696
  have htrace : WordTrace (prefixWord ++ tailWord_3562696) baseStart_3562696 baseEnd_3562696 := by
    simpa [prefixWord, tailWord_3562696, baseEnd_3562696] using wordTrace_append hprefix tailTrace_3562696
  have hstable : (prefixWord ++ tailWord_3562696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562696).length < 2 ^ (prefixWord ++ tailWord_3562696).sum := by decide
  have hdescent : baseEnd_3562696 < baseStart_3562696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562701 : List Nat := [1, 6, 2, 2, 1, 1, 3, 2, 5]
def baseStart_3562701 : Nat := 118140960795 + 3562701 * 2 ^ 59
def prefixEnd_3562701 : Nat := 4983230072969 + 3 ^ 40 * 3562701 * 2
def baseEnd_3562701 : Nat := 203264226805996738850327

theorem tailTrace_3562701 : CollatzResearch.WordTrace tailWord_3562701 prefixEnd_3562701 203264226805996738850327 := by
  unfold tailWord_3562701
  simp only [CollatzResearch.WordTrace]
  refine ⟨129942380665950212733863957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86628253777300141822575971 129942380665950212733863957)
  ·
    refine ⟨6091049093716416221899873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 129942380665950212733863957 6091049093716416221899873)
    ·
      refine ⟨4568286820287312166424905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6091049093716416221899873 4568286820287312166424905)
      ·
        refine ⟨3426215115215484124818679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4568286820287312166424905 3426215115215484124818679)
        ·
          refine ⟨5139322672823226187228019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3426215115215484124818679 5139322672823226187228019)
          ·
            refine ⟨7708984009234839280842029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5139322672823226187228019 7708984009234839280842029)
            ·
              refine ⟨2890869003463064730315761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7708984009234839280842029 2890869003463064730315761)
              ·
                refine ⟨2168151752597298547736821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2890869003463064730315761 2168151752597298547736821)
                ·
                  refine ⟨203264226805996738850327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2168151752597298547736821 203264226805996738850327)
                  ·
                    rfl

theorem cell23_3562701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_3562701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3562701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3562701 prefixEnd_3562701 := by exact prefixLift 3562701
  have htrace : WordTrace (prefixWord ++ tailWord_3562701) baseStart_3562701 baseEnd_3562701 := by
    simpa [prefixWord, tailWord_3562701, baseEnd_3562701] using wordTrace_append hprefix tailTrace_3562701
  have hstable : (prefixWord ++ tailWord_3562701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562701).length < 2 ^ (prefixWord ++ tailWord_3562701).sum := by decide
  have hdescent : baseEnd_3562701 < baseStart_3562701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562794 : List Nat := [3, 1, 4, 2, 1, 1, 3, 1, 2, 3, 2]
def baseStart_3562794 : Nat := 118140960795 + 3562794 * 2 ^ 59
def prefixEnd_3562794 : Nat := 4983230072969 + 3 ^ 40 * 3562794 * 2
def baseEnd_3562794 : Nat := 1829425794954838785790015

theorem tailTrace_3562794 : CollatzResearch.WordTrace tailWord_3562794 prefixEnd_3562794 1829425794954838785790015 := by
  unfold tailWord_3562794
  simp only [CollatzResearch.WordTrace]
  refine ⟨32486443163653322404249859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86630515103075526411332957 32486443163653322404249859)
  ·
    refine ⟨48729664745479983606374789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32486443163653322404249859 48729664745479983606374789)
    ·
      refine ⟨9136812139777496926195273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48729664745479983606374789 9136812139777496926195273)
      ·
        refine ⟨6852609104833122694646455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9136812139777496926195273 6852609104833122694646455)
        ·
          refine ⟨10278913657249684041969683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6852609104833122694646455 10278913657249684041969683)
          ·
            refine ⟨15418370485874526062954525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10278913657249684041969683 15418370485874526062954525)
            ·
              refine ⟨5781888932202947273607947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15418370485874526062954525 5781888932202947273607947)
              ·
                refine ⟨8672833398304420910411921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5781888932202947273607947 8672833398304420910411921)
                ·
                  refine ⟨6504625048728315682808941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8672833398304420910411921 6504625048728315682808941)
                  ·
                    refine ⟨2439234393273118381053353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6504625048728315682808941 2439234393273118381053353)
                    ·
                      refine ⟨1829425794954838785790015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2439234393273118381053353 1829425794954838785790015)
                      ·
                        rfl

theorem cell23_3562794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_3562794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3562794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3562794 prefixEnd_3562794 := by exact prefixLift 3562794
  have htrace : WordTrace (prefixWord ++ tailWord_3562794) baseStart_3562794 baseEnd_3562794 := by
    simpa [prefixWord, tailWord_3562794, baseEnd_3562794] using wordTrace_append hprefix tailTrace_3562794
  have hstable : (prefixWord ++ tailWord_3562794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562794).length < 2 ^ (prefixWord ++ tailWord_3562794).sum := by decide
  have hdescent : baseEnd_3562794 < baseStart_3562794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562817 : List Nat := [1, 2, 5, 2, 1, 2, 1, 1, 4, 4]
def baseStart_3562817 : Nat := 118140960795 + 3562817 * 2 ^ 59
def prefixEnd_3562817 : Nat := 4983230072969 + 3 ^ 40 * 3562817 * 2
def baseEnd_3562817 : Nat := 609812535003297398600803

theorem tailTrace_3562817 : CollatzResearch.WordTrace tailWord_3562817 prefixEnd_3562817 609812535003297398600803 := by
  unfold tailWord_3562817
  simp only [CollatzResearch.WordTrace]
  refine ⟨129946611533529964545086705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86631074355686643030057803 129946611533529964545086705)
  ·
    refine ⟨97459958650147473408815029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129946611533529964545086705 97459958650147473408815029)
    ·
      refine ⟨9136871123451325632076409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97459958650147473408815029 9136871123451325632076409)
      ·
        refine ⟨6852653342588494224057307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9136871123451325632076409 6852653342588494224057307)
        ·
          refine ⟨10278980013882741336085961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6852653342588494224057307 10278980013882741336085961)
          ·
            refine ⟨7709235010412056002064471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10278980013882741336085961 7709235010412056002064471)
            ·
              refine ⟨11563852515618084003096707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7709235010412056002064471 11563852515618084003096707)
              ·
                refine ⟨17345778773427126004645061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11563852515618084003096707 17345778773427126004645061)
                ·
                  refine ⟨3252333520017586125870949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17345778773427126004645061 3252333520017586125870949)
                  ·
                    refine ⟨609812535003297398600803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3252333520017586125870949 609812535003297398600803)
                    ·
                      rfl

theorem cell23_3562817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_3562817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3562817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3562817 prefixEnd_3562817 := by exact prefixLift 3562817
  have htrace : WordTrace (prefixWord ++ tailWord_3562817) baseStart_3562817 baseEnd_3562817 := by
    simpa [prefixWord, tailWord_3562817, baseEnd_3562817] using wordTrace_append hprefix tailTrace_3562817
  have hstable : (prefixWord ++ tailWord_3562817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562817).length < 2 ^ (prefixWord ++ tailWord_3562817).sum := by decide
  have hdescent : baseEnd_3562817 < baseStart_3562817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562837 : List Nat := [1, 3, 2, 2, 3, 3, 1, 1, 1, 2, 4]
def baseStart_3562837 : Nat := 118140960795 + 3562837 * 2 ^ 59
def prefixEnd_3562837 : Nat := 4983230072969 + 3 ^ 40 * 3562837 * 2
def baseEnd_3562837 : Nat := 1829447874622982117552317

theorem tailTrace_3562837 : CollatzResearch.WordTrace tailWord_3562837 prefixEnd_3562837 1829447874622982117552317 := by
  unfold tailWord_3562837
  simp only [CollatzResearch.WordTrace]
  refine ⟨129947340993457507960814765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86631560662305005307209843 129947340993457507960814765)
  ·
    refine ⟨48730252872546565485305537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129947340993457507960814765 48730252872546565485305537)
    ·
      refine ⟨36547689654409924113979153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48730252872546565485305537 36547689654409924113979153)
      ·
        refine ⟨27410767240807443085484365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36547689654409924113979153 27410767240807443085484365)
        ·
          refine ⟨10279037715302791157056637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27410767240807443085484365 10279037715302791157056637)
          ·
            refine ⟨3854639143238546683896239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10279037715302791157056637 3854639143238546683896239)
            ·
              refine ⟨5781958714857820025844359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3854639143238546683896239 5781958714857820025844359)
              ·
                refine ⟨8672938072286730038766539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5781958714857820025844359 8672938072286730038766539)
                ·
                  refine ⟨13009407108430095058149809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8672938072286730038766539 13009407108430095058149809)
                  ·
                    refine ⟨9757055331322571293612357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13009407108430095058149809 9757055331322571293612357)
                    ·
                      refine ⟨1829447874622982117552317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9757055331322571293612357 1829447874622982117552317)
                      ·
                        rfl

theorem cell23_3562837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_3562837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3562837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3562837 prefixEnd_3562837 := by exact prefixLift 3562837
  have htrace : WordTrace (prefixWord ++ tailWord_3562837) baseStart_3562837 baseEnd_3562837 := by
    simpa [prefixWord, tailWord_3562837, baseEnd_3562837] using wordTrace_append hprefix tailTrace_3562837
  have hstable : (prefixWord ++ tailWord_3562837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562837).length < 2 ^ (prefixWord ++ tailWord_3562837).sum := by decide
  have hdescent : baseEnd_3562837 < baseStart_3562837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562838 : List Nat := [5, 2, 3, 1, 1, 1, 2, 2, 1, 5]
def baseStart_3562838 : Nat := 118140960795 + 3562838 * 2 ^ 59
def prefixEnd_3562838 : Nat := 4983230072969 + 3 ^ 40 * 3562838 * 2
def baseEnd_3562838 : Nat := 609816129367878871213271

theorem tailTrace_3562838 : CollatzResearch.WordTrace tailWord_3562838 prefixEnd_3562838 609816129367878871213271 := by
  unfold tailWord_3562838
  simp only [CollatzResearch.WordTrace]
  refine ⟨8121711091653367820725073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86631584977635923421067445 8121711091653367820725073)
  ·
    refine ⟨6091283318740025865543805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8121711091653367820725073 6091283318740025865543805)
    ·
      refine ⟨2284231244527509699578927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6091283318740025865543805 2284231244527509699578927)
      ·
        refine ⟨3426346866791264549368391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2284231244527509699578927 3426346866791264549368391)
        ·
          refine ⟨5139520300186896824052587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3426346866791264549368391 5139520300186896824052587)
          ·
            refine ⟨7709280450280345236078881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5139520300186896824052587 7709280450280345236078881)
            ·
              refine ⟨5781960337710258927059161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7709280450280345236078881 5781960337710258927059161)
              ·
                refine ⟨4336470253282694195294371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5781960337710258927059161 4336470253282694195294371)
                ·
                  refine ⟨6504705379924041292941557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4336470253282694195294371 6504705379924041292941557)
                  ·
                    refine ⟨609816129367878871213271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6504705379924041292941557 609816129367878871213271)
                    ·
                      rfl

theorem cell23_3562838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_3562838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3562838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3562838 prefixEnd_3562838 := by exact prefixLift 3562838
  have htrace : WordTrace (prefixWord ++ tailWord_3562838) baseStart_3562838 baseEnd_3562838 := by
    simpa [prefixWord, tailWord_3562838, baseEnd_3562838] using wordTrace_append hprefix tailTrace_3562838
  have hstable : (prefixWord ++ tailWord_3562838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562838).length < 2 ^ (prefixWord ++ tailWord_3562838).sum := by decide
  have hdescent : baseEnd_3562838 < baseStart_3562838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562853 : List Nat := [1, 3, 1, 3, 1, 2, 1, 1, 1, 4, 5]
def baseStart_3562853 : Nat := 118140960795 + 3562853 * 2 ^ 59
def prefixEnd_3562853 : Nat := 4983230072969 + 3 ^ 40 * 3562853 * 2
def baseEnd_3562853 : Nat := 1829456090313454054952243

theorem tailTrace_3562853 : CollatzResearch.WordTrace tailWord_3562853 prefixEnd_3562853 1829456090313454054952243 := by
  unfold tailWord_3562853
  simp only [CollatzResearch.WordTrace]
  refine ⟨129947924561399542693397213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86631949707599695128931475 129947924561399542693397213)
  ·
    refine ⟨48730471710524828510023955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129947924561399542693397213 48730471710524828510023955)
    ·
      refine ⟨73095707565787242765035933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48730471710524828510023955 73095707565787242765035933)
      ·
        refine ⟨27410890337170216036888475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73095707565787242765035933 27410890337170216036888475)
        ·
          refine ⟨41116335505755324055332713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27410890337170216036888475 41116335505755324055332713)
          ·
            refine ⟨30837251629316493041499535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41116335505755324055332713 30837251629316493041499535)
            ·
              refine ⟨46255877443974739562249303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30837251629316493041499535 46255877443974739562249303)
              ·
                refine ⟨69383816165962109343373955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46255877443974739562249303 69383816165962109343373955)
                ·
                  refine ⟨104075724248943164015060933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69383816165962109343373955 104075724248943164015060933)
                  ·
                    refine ⟨19514198296676843252823925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 104075724248943164015060933 19514198296676843252823925)
                    ·
                      refine ⟨1829456090313454054952243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19514198296676843252823925 1829456090313454054952243)
                      ·
                        rfl

theorem cell23_3562853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_3562853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3562853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3562853 prefixEnd_3562853 := by exact prefixLift 3562853
  have htrace : WordTrace (prefixWord ++ tailWord_3562853) baseStart_3562853 baseEnd_3562853 := by
    simpa [prefixWord, tailWord_3562853, baseEnd_3562853] using wordTrace_append hprefix tailTrace_3562853
  have hstable : (prefixWord ++ tailWord_3562853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562853).length < 2 ^ (prefixWord ++ tailWord_3562853).sum := by decide
  have hdescent : baseEnd_3562853 < baseStart_3562853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562873 : List Nat := [1, 2, 1, 3, 2, 1, 2, 1, 4, 6]
def baseStart_3562873 : Nat := 118140960795 + 3562873 * 2 ^ 59
def prefixEnd_3562873 : Nat := 4983230072969 + 3 ^ 40 * 3562873 * 2
def baseEnd_3562873 : Nat := 609822119975514658900717

theorem tailTrace_3562873 : CollatzResearch.WordTrace tailWord_3562873 prefixEnd_3562873 609822119975514658900717 := by
  unfold tailWord_3562873
  simp only [CollatzResearch.WordTrace]
  refine ⟨129948654021327086109125273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86632436014218057406083515 129948654021327086109125273)
  ·
    refine ⟨97461490515995314581843955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129948654021327086109125273 97461490515995314581843955)
    ·
      refine ⟨146192235773992971872765933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97461490515995314581843955 146192235773992971872765933)
      ·
        refine ⟨54822088415247364452287225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146192235773992971872765933 54822088415247364452287225)
        ·
          refine ⟨41116566311435523339215419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54822088415247364452287225 41116566311435523339215419)
          ·
            refine ⟨61674849467153285008823129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41116566311435523339215419 61674849467153285008823129)
            ·
              refine ⟨46256137100364963756617347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61674849467153285008823129 46256137100364963756617347)
              ·
                refine ⟨69384205650547445634926021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46256137100364963756617347 69384205650547445634926021)
                ·
                  refine ⟨13009538559477646056548629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69384205650547445634926021 13009538559477646056548629)
                  ·
                    refine ⟨609822119975514658900717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13009538559477646056548629 609822119975514658900717)
                    ·
                      rfl

theorem cell23_3562873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4, 6].length) (baseStart_3562873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3562873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3562873 prefixEnd_3562873 := by exact prefixLift 3562873
  have htrace : WordTrace (prefixWord ++ tailWord_3562873) baseStart_3562873 baseEnd_3562873 := by
    simpa [prefixWord, tailWord_3562873, baseEnd_3562873] using wordTrace_append hprefix tailTrace_3562873
  have hstable : (prefixWord ++ tailWord_3562873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562873).length < 2 ^ (prefixWord ++ tailWord_3562873).sum := by decide
  have hdescent : baseEnd_3562873 < baseStart_3562873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562903 : List Nat := [1, 1, 3, 3, 1, 1, 1, 3, 9]
def baseStart_3562903 : Nat := 118140960795 + 3562903 * 2 ^ 59
def prefixEnd_3562903 : Nat := 4983230072969 + 3 ^ 40 * 3562903 * 2
def baseEnd_3562903 : Nat := 203275751594019873258557

theorem tailTrace_3562903 : CollatzResearch.WordTrace tailWord_3562903 prefixEnd_3562903 203275751594019873258557 := by
  unfold tailWord_3562903
  simp only [CollatzResearch.WordTrace]
  refine ⟨129949748211218401232717363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86633165474145600821811575 129949748211218401232717363)
  ·
    refine ⟨194924622316827601849076045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129949748211218401232717363 194924622316827601849076045)
    ·
      refine ⟨73096733368810350693403517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194924622316827601849076045 73096733368810350693403517)
      ·
        refine ⟨27411275013303881510026319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73096733368810350693403517 27411275013303881510026319)
        ·
          refine ⟨41116912519955822265039479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27411275013303881510026319 41116912519955822265039479)
          ·
            refine ⟨61675368779933733397559219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41116912519955822265039479 61675368779933733397559219)
            ·
              refine ⟨92513053169900600096338829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61675368779933733397559219 92513053169900600096338829)
              ·
                refine ⟨34692394938712725036127061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92513053169900600096338829 34692394938712725036127061)
                ·
                  refine ⟨203275751594019873258557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 34692394938712725036127061 203275751594019873258557)
                  ·
                    rfl

theorem cell23_3562903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 9].length) (baseStart_3562903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3562903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3562903 prefixEnd_3562903 := by exact prefixLift 3562903
  have htrace : WordTrace (prefixWord ++ tailWord_3562903) baseStart_3562903 baseEnd_3562903 := by
    simpa [prefixWord, tailWord_3562903, baseEnd_3562903] using wordTrace_append hprefix tailTrace_3562903
  have hstable : (prefixWord ++ tailWord_3562903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562903).length < 2 ^ (prefixWord ++ tailWord_3562903).sum := by decide
  have hdescent : baseEnd_3562903 < baseStart_3562903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3562914 : List Nat := [3, 3, 1, 2, 1, 3, 1, 2, 1, 4, 2]
def baseStart_3562914 : Nat := 118140960795 + 3562914 * 2 ^ 59
def prefixEnd_3562914 : Nat := 4983230072969 + 3 ^ 40 * 3562914 * 2
def baseEnd_3562914 : Nat := 1829487412633378316289463

theorem tailTrace_3562914 : CollatzResearch.WordTrace tailWord_3562914 prefixEnd_3562914 1829487412633378316289463 := by
  unfold tailWord_3562914
  simp only [CollatzResearch.WordTrace]
  refine ⟨32487537353544637527841949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86633432942785700074245197 32487537353544637527841949)
  ·
    refine ⟨12182826507579239072940731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32487537353544637527841949 12182826507579239072940731)
    ·
      refine ⟨18274239761368858609411097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12182826507579239072940731 18274239761368858609411097)
      ·
        refine ⟨13705679821026643957058323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18274239761368858609411097 13705679821026643957058323)
        ·
          refine ⟨20558519731539965935587485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13705679821026643957058323 20558519731539965935587485)
          ·
            refine ⟨7709444899327487225845307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20558519731539965935587485 7709444899327487225845307)
            ·
              refine ⟨11564167348991230838767961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7709444899327487225845307 11564167348991230838767961)
              ·
                refine ⟨8673125511743423129075971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11564167348991230838767961 8673125511743423129075971)
                ·
                  refine ⟨13009688267615134693613957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8673125511743423129075971 13009688267615134693613957)
                  ·
                    refine ⟨2439316550177837755052617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13009688267615134693613957 2439316550177837755052617)
                    ·
                      refine ⟨1829487412633378316289463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2439316550177837755052617 1829487412633378316289463)
                      ·
                        rfl

theorem cell23_3562914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_3562914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3562914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3562914 prefixEnd_3562914 := by exact prefixLift 3562914
  have htrace : WordTrace (prefixWord ++ tailWord_3562914) baseStart_3562914 baseEnd_3562914 := by
    simpa [prefixWord, tailWord_3562914, baseEnd_3562914] using wordTrace_append hprefix tailTrace_3562914
  have hstable : (prefixWord ++ tailWord_3562914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3562914).length < 2 ^ (prefixWord ++ tailWord_3562914).sum := by decide
  have hdescent : baseEnd_3562914 < baseStart_3562914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3562914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563048 : List Nat := [2, 1, 5, 2, 3, 1, 1, 1, 3, 4]
def baseStart_3563048 : Nat := 118140960795 + 3563048 * 2 ^ 59
def prefixEnd_3563048 : Nat := 4983230072969 + 3 ^ 40 * 3563048 * 2
def baseEnd_3563048 : Nat := 609852073013693597337949

theorem tailTrace_3563048 : CollatzResearch.WordTrace tailWord_3563048 prefixEnd_3563048 609852073013693597337949 := by
  unfold tailWord_3563048
  simp only [CollatzResearch.WordTrace]
  refine ⟨64977518397846545498372899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86636691197128727331163865 64977518397846545498372899)
  ·
    refine ⟨97466277596769818247559349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64977518397846545498372899 97466277596769818247559349)
    ·
      refine ⟨9137463524697170460708689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97466277596769818247559349 9137463524697170460708689)
      ·
        refine ⟨6853097643522877845531517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9137463524697170460708689 6853097643522877845531517)
        ·
          refine ⟨2569911616321079192074319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6853097643522877845531517 2569911616321079192074319)
          ·
            refine ⟨3854867424481618788111479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2569911616321079192074319 3854867424481618788111479)
            ·
              refine ⟨5782301136722428182167219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3854867424481618788111479 5782301136722428182167219)
              ·
                refine ⟨8673451705083642273250829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5782301136722428182167219 8673451705083642273250829)
                ·
                  refine ⟨3252544389406365852469061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8673451705083642273250829 3252544389406365852469061)
                  ·
                    refine ⟨609852073013693597337949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3252544389406365852469061 609852073013693597337949)
                    ·
                      rfl

theorem cell23_3563048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_3563048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3563048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3563048 prefixEnd_3563048 := by exact prefixLift 3563048
  have htrace : WordTrace (prefixWord ++ tailWord_3563048) baseStart_3563048 baseEnd_3563048 := by
    simpa [prefixWord, tailWord_3563048, baseEnd_3563048] using wordTrace_append hprefix tailTrace_3563048
  have hstable : (prefixWord ++ tailWord_3563048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563048).length < 2 ^ (prefixWord ++ tailWord_3563048).sum := by decide
  have hdescent : baseEnd_3563048 < baseStart_3563048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563077 : List Nat := [1, 3, 1, 1, 1, 4, 3, 1, 3, 1, 4]
def baseStart_3563077 : Nat := 118140960795 + 3563077 * 2 ^ 59
def prefixEnd_3563077 : Nat := 4983230072969 + 3 ^ 40 * 3563077 * 2
def baseEnd_3563077 : Nat := 1829571109980061178551213

theorem tailTrace_3563077 : CollatzResearch.WordTrace tailWord_3563077 prefixEnd_3563077 1829571109980061178551213 := by
  unfold tailWord_3563077
  simp only [CollatzResearch.WordTrace]
  refine ⟨129956094512588028949551485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86637396341725352633034323 129956094512588028949551485)
  ·
    refine ⟨48733535442220510856081807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129956094512588028949551485 48733535442220510856081807)
    ·
      refine ⟨73100303163330766284122711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48733535442220510856081807 73100303163330766284122711)
      ·
        refine ⟨109650454744996149426184067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73100303163330766284122711 109650454744996149426184067)
        ·
          refine ⟨164475682117494224139276101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109650454744996149426184067 164475682117494224139276101)
          ·
            refine ⟨30839190397030167026114269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 164475682117494224139276101 30839190397030167026114269)
            ·
              refine ⟨11564696398886312634792851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30839190397030167026114269 11564696398886312634792851)
              ·
                refine ⟨17347044598329468952189277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11564696398886312634792851 17347044598329468952189277)
                ·
                  refine ⟨6505141724373550857070979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17347044598329468952189277 6505141724373550857070979)
                  ·
                    refine ⟨9757712586560326285606469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6505141724373550857070979 9757712586560326285606469)
                    ·
                      refine ⟨1829571109980061178551213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9757712586560326285606469 1829571109980061178551213)
                      ·
                        rfl

theorem cell23_3563077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 3, 1, 4].length) (baseStart_3563077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3563077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3563077 prefixEnd_3563077 := by exact prefixLift 3563077
  have htrace : WordTrace (prefixWord ++ tailWord_3563077) baseStart_3563077 baseEnd_3563077 := by
    simpa [prefixWord, tailWord_3563077, baseEnd_3563077] using wordTrace_append hprefix tailTrace_3563077
  have hstable : (prefixWord ++ tailWord_3563077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563077).length < 2 ^ (prefixWord ++ tailWord_3563077).sum := by decide
  have hdescent : baseEnd_3563077 < baseStart_3563077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563080 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 2, 5, 5]
def baseStart_3563080 : Nat := 118140960795 + 3563080 * 2 ^ 59
def prefixEnd_3563080 : Nat := 4983230072969 + 3 ^ 40 * 3563080 * 2
def baseEnd_3563080 : Nat := 1829572650422024666813699

theorem tailTrace_3563080 : CollatzResearch.WordTrace tailWord_3563080 prefixEnd_3563080 1829572650422024666813699 := by
  unfold tailWord_3563080
  simp only [CollatzResearch.WordTrace]
  refine ⟨64978101965788580230955347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86637469287718106974607129 64978101965788580230955347)
  ·
    refine ⟨97467152948682870346433021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64978101965788580230955347 97467152948682870346433021)
    ·
      refine ⟨36550182355756076379912383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97467152948682870346433021 36550182355756076379912383)
      ·
        refine ⟨54825273533634114569868575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36550182355756076379912383 54825273533634114569868575)
        ·
          refine ⟨82237910300451171854802863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54825273533634114569868575 82237910300451171854802863)
          ·
            refine ⟨123356865450676757782204295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82237910300451171854802863 123356865450676757782204295)
            ·
              refine ⟨185035298176015136673306443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123356865450676757782204295 185035298176015136673306443)
              ·
                refine ⟨277552947264022705009959665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185035298176015136673306443 277552947264022705009959665)
                ·
                  refine ⟨208164710448017028757469749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 277552947264022705009959665 208164710448017028757469749)
                  ·
                    refine ⟨19515441604501596446012789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 208164710448017028757469749 19515441604501596446012789)
                    ·
                      refine ⟨1829572650422024666813699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19515441604501596446012789 1829572650422024666813699)
                      ·
                        rfl

theorem cell23_3563080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_3563080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3563080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3563080 prefixEnd_3563080 := by exact prefixLift 3563080
  have htrace : WordTrace (prefixWord ++ tailWord_3563080) baseStart_3563080 baseEnd_3563080 := by
    simpa [prefixWord, tailWord_3563080, baseEnd_3563080] using wordTrace_append hprefix tailTrace_3563080
  have hstable : (prefixWord ++ tailWord_3563080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563080).length < 2 ^ (prefixWord ++ tailWord_3563080).sum := by decide
  have hdescent : baseEnd_3563080 < baseStart_3563080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563114 : List Nat := [3, 1, 3, 2, 1, 2, 1, 2, 3, 2, 3]
def baseStart_3563114 : Nat := 118140960795 + 3563114 * 2 ^ 59
def prefixEnd_3563114 : Nat := 4983230072969 + 3 ^ 40 * 3563114 * 2
def baseEnd_3563114 : Nat := 1829590108764277533788543

theorem tailTrace_3563114 : CollatzResearch.WordTrace tailWord_3563114 prefixEnd_3563114 1829590108764277533788543 := by
  unfold tailWord_3563114
  simp only [CollatzResearch.WordTrace]
  refine ⟨32489361003363496067162099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86638296008969322845765597 32489361003363496067162099)
  ·
    refine ⟨48734041505045244100743149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32489361003363496067162099 48734041505045244100743149)
    ·
      refine ⟨18275265564391966537778681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48734041505045244100743149 18275265564391966537778681)
      ·
        refine ⟨13706449173293974903334011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18275265564391966537778681 13706449173293974903334011)
        ·
          refine ⟨20559673759940962355001017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13706449173293974903334011 20559673759940962355001017)
          ·
            refine ⟨15419755319955721766250763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20559673759940962355001017 15419755319955721766250763)
            ·
              refine ⟨23129632979933582649376145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15419755319955721766250763 23129632979933582649376145)
              ·
                refine ⟨17347224734950186987032109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23129632979933582649376145 17347224734950186987032109)
                ·
                  refine ⟨6505209275606320120137041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17347224734950186987032109 6505209275606320120137041)
                  ·
                    refine ⟨4878906956704740090102781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6505209275606320120137041 4878906956704740090102781)
                    ·
                      refine ⟨1829590108764277533788543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4878906956704740090102781 1829590108764277533788543)
                      ·
                        rfl

theorem cell23_3563114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_3563114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3563114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3563114 prefixEnd_3563114 := by exact prefixLift 3563114
  have htrace : WordTrace (prefixWord ++ tailWord_3563114) baseStart_3563114 baseEnd_3563114 := by
    simpa [prefixWord, tailWord_3563114, baseEnd_3563114] using wordTrace_append hprefix tailTrace_3563114
  have hstable : (prefixWord ++ tailWord_3563114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563114).length < 2 ^ (prefixWord ++ tailWord_3563114).sum := by decide
  have hdescent : baseEnd_3563114 < baseStart_3563114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563187 : List Nat := [1, 1, 1, 2, 3, 3, 2, 2, 2, 1, 5]
def baseStart_3563187 : Nat := 118140960795 + 3563187 * 2 ^ 59
def prefixEnd_3563187 : Nat := 4983230072969 + 3 ^ 40 * 3563187 * 2
def baseEnd_3563187 : Nat := 1829627592852055748175707

theorem tailTrace_3563187 : CollatzResearch.WordTrace tailWord_3563187 prefixEnd_3563187 1829627592852055748175707 := by
  unfold tailWord_3563187
  simp only [CollatzResearch.WordTrace]
  refine ⟨129960106542189517736055815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86640071028126345157370543 129960106542189517736055815)
  ·
    refine ⟨194940159813284276604083723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129960106542189517736055815 194940159813284276604083723)
    ·
      refine ⟨292410239719926414906125585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194940159813284276604083723 292410239719926414906125585)
      ·
        refine ⟨219307679789944811179594189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292410239719926414906125585 219307679789944811179594189)
        ·
          refine ⟨82240379921229304192347821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 219307679789944811179594189 82240379921229304192347821)
          ·
            refine ⟨30840142470460989072130433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82240379921229304192347821 30840142470460989072130433)
            ·
              refine ⟨23130106852845741804097825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30840142470460989072130433 23130106852845741804097825)
              ·
                refine ⟨17347580139634306353073369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23130106852845741804097825 17347580139634306353073369)
                ·
                  refine ⟨13010685104725729764805027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17347580139634306353073369 13010685104725729764805027)
                  ·
                    refine ⟨19516027657088594647207541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13010685104725729764805027 19516027657088594647207541)
                    ·
                      refine ⟨1829627592852055748175707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19516027657088594647207541 1829627592852055748175707)
                      ·
                        rfl

theorem cell23_3563187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2, 1, 5].length) (baseStart_3563187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3563187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3563187 prefixEnd_3563187 := by exact prefixLift 3563187
  have htrace : WordTrace (prefixWord ++ tailWord_3563187) baseStart_3563187 baseEnd_3563187 := by
    simpa [prefixWord, tailWord_3563187, baseEnd_3563187] using wordTrace_append hprefix tailTrace_3563187
  have hstable : (prefixWord ++ tailWord_3563187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563187).length < 2 ^ (prefixWord ++ tailWord_3563187).sum := by decide
  have hdescent : baseEnd_3563187 < baseStart_3563187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563204 : List Nat := [2, 3, 3, 1, 1, 1, 3, 1, 2, 1, 5]
def baseStart_3563204 : Nat := 118140960795 + 3563204 * 2 ^ 59
def prefixEnd_3563204 : Nat := 4983230072969 + 3 ^ 40 * 3563204 * 2
def baseEnd_3563204 : Nat := 1829636322023182181663129

theorem tailTrace_3563204 : CollatzResearch.WordTrace tailWord_3563204 prefixEnd_3563204 1829636322023182181663129 := by
  unfold tailWord_3563204
  simp only [CollatzResearch.WordTrace]
  refine ⟨64980363291563964819712333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86640484388751953092949777 64980363291563964819712333)
  ·
    refine ⟨24367636234336486807392125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64980363291563964819712333 24367636234336486807392125)
    ·
      refine ⟨9137863587876182552772047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24367636234336486807392125 9137863587876182552772047)
      ·
        refine ⟨13706795381814273829158071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9137863587876182552772047 13706795381814273829158071)
        ·
          refine ⟨20560193072721410743737107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13706795381814273829158071 20560193072721410743737107)
          ·
            refine ⟨30840289609082116115605661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20560193072721410743737107 30840289609082116115605661)
            ·
              refine ⟨11565108603405793543352123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30840289609082116115605661 11565108603405793543352123)
              ·
                refine ⟨17347662905108690315028185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11565108603405793543352123 17347662905108690315028185)
                ·
                  refine ⟨13010747178831517736271139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17347662905108690315028185 13010747178831517736271139)
                  ·
                    refine ⟨19516120768247276604406709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13010747178831517736271139 19516120768247276604406709)
                    ·
                      refine ⟨1829636322023182181663129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19516120768247276604406709 1829636322023182181663129)
                      ·
                        rfl

theorem cell23_3563204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_3563204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3563204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3563204 prefixEnd_3563204 := by exact prefixLift 3563204
  have htrace : WordTrace (prefixWord ++ tailWord_3563204) baseStart_3563204 baseEnd_3563204 := by
    simpa [prefixWord, tailWord_3563204, baseEnd_3563204] using wordTrace_append hprefix tailTrace_3563204
  have hstable : (prefixWord ++ tailWord_3563204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563204).length < 2 ^ (prefixWord ++ tailWord_3563204).sum := by decide
  have hdescent : baseEnd_3563204 < baseStart_3563204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563218 : List Nat := [3, 2, 2, 2, 2, 1, 2, 1, 4, 2, 2]
def baseStart_3563218 : Nat := 118140960795 + 3563218 * 2 ^ 59
def prefixEnd_3563218 : Nat := 4983230072969 + 3 ^ 40 * 3563218 * 2
def baseEnd_3563218 : Nat := 1829643510752345126888065

theorem tailTrace_3563218 : CollatzResearch.WordTrace tailWord_3563218 prefixEnd_3563218 1829643510752345126888065 := by
  unfold tailWord_3563218
  simp only [CollatzResearch.WordTrace]
  refine ⟨32490309301269302507608577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86640824803384806686956205 32490309301269302507608577)
  ·
    refine ⟨24367731975951976880706433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32490309301269302507608577 24367731975951976880706433)
    ·
      refine ⟨18275798981963982660529825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24367731975951976880706433 18275798981963982660529825)
      ·
        refine ⟨13706849236472986995397369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18275798981963982660529825 13706849236472986995397369)
        ·
          refine ⟨10280136927354740246548027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13706849236472986995397369 10280136927354740246548027)
          ·
            refine ⟨15420205391032110369822041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10280136927354740246548027 15420205391032110369822041)
            ·
              refine ⟨11565154043274082777366531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15420205391032110369822041 11565154043274082777366531)
              ·
                refine ⟨17347731064911124166049797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11565154043274082777366531 17347731064911124166049797)
                ·
                  refine ⟨3252699574670835781134337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17347731064911124166049797 3252699574670835781134337)
                  ·
                    refine ⟨2439524681003126835850753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3252699574670835781134337 2439524681003126835850753)
                    ·
                      refine ⟨1829643510752345126888065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2439524681003126835850753 1829643510752345126888065)
                      ·
                        rfl

theorem cell23_3563218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_3563218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3563218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3563218 prefixEnd_3563218 := by exact prefixLift 3563218
  have htrace : WordTrace (prefixWord ++ tailWord_3563218) baseStart_3563218 baseEnd_3563218 := by
    simpa [prefixWord, tailWord_3563218, baseEnd_3563218] using wordTrace_append hprefix tailTrace_3563218
  have hstable : (prefixWord ++ tailWord_3563218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563218).length < 2 ^ (prefixWord ++ tailWord_3563218).sum := by decide
  have hdescent : baseEnd_3563218 < baseStart_3563218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563229 : List Nat := [1, 4, 3, 3, 2, 1, 2, 1, 2, 1, 3]
def baseStart_3563229 : Nat := 118140960795 + 3563229 * 2 ^ 59
def prefixEnd_3563229 : Nat := 4983230072969 + 3 ^ 40 * 3563229 * 2
def baseEnd_3563229 : Nat := 1829649159039544583850515

theorem tailTrace_3563229 : CollatzResearch.WordTrace tailWord_3563229 prefixEnd_3563229 1829649159039544583850515 := by
  unfold tailWord_3563229
  simp only [CollatzResearch.WordTrace]
  refine ⟨129961638408037358909084741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86641092272024905939389827 129961638408037358909084741)
  ·
    refine ⟨24367807201507004795453389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129961638408037358909084741 24367807201507004795453389)
    ·
      refine ⟨9137927700565126798295021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24367807201507004795453389 9137927700565126798295021)
      ·
        refine ⟨3426722887711922549360633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9137927700565126798295021 3426722887711922549360633)
        ·
          refine ⟨2570042165783941912020475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3426722887711922549360633 2570042165783941912020475)
          ·
            refine ⟨3855063248675912868030713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2570042165783941912020475 3855063248675912868030713)
            ·
              refine ⟨2891297436506934651023035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3855063248675912868030713 2891297436506934651023035)
              ·
                refine ⟨4336946154760401976534553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2891297436506934651023035 4336946154760401976534553)
                ·
                  refine ⟨3252709616070301482400915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4336946154760401976534553 3252709616070301482400915)
                  ·
                    refine ⟨4879064424105452223601373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3252709616070301482400915 4879064424105452223601373)
                    ·
                      refine ⟨1829649159039544583850515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4879064424105452223601373 1829649159039544583850515)
                      ·
                        rfl

theorem cell23_3563229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_3563229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3563229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3563229 prefixEnd_3563229 := by exact prefixLift 3563229
  have htrace : WordTrace (prefixWord ++ tailWord_3563229) baseStart_3563229 baseEnd_3563229 := by
    simpa [prefixWord, tailWord_3563229, baseEnd_3563229] using wordTrace_append hprefix tailTrace_3563229
  have hstable : (prefixWord ++ tailWord_3563229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563229).length < 2 ^ (prefixWord ++ tailWord_3563229).sum := by decide
  have hdescent : baseEnd_3563229 < baseStart_3563229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563235 : List Nat := [1, 1, 1, 7, 2, 1, 1, 3, 2, 2, 2]
def baseStart_3563235 : Nat := 118140960795 + 3563235 * 2 ^ 59
def prefixEnd_3563235 : Nat := 4983230072969 + 3 ^ 40 * 3563235 * 2
def baseEnd_3563235 : Nat := 1829652239923471560375487

theorem tailTrace_3563235 : CollatzResearch.WordTrace tailWord_3563235 prefixEnd_3563235 1829652239923471560375487 := by
  unfold tailWord_3563235
  simp only [CollatzResearch.WordTrace]
  refine ⟨129961857246015621933803159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86641238164010414622535439 129961857246015621933803159)
  ·
    refine ⟨194942785869023432900704739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129961857246015621933803159 194942785869023432900704739)
    ·
      refine ⟨292414178803535149351057109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194942785869023432900704739 292414178803535149351057109)
      ·
        refine ⟨6853457315707855062915401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 292414178803535149351057109 6853457315707855062915401)
        ·
          refine ⟨5140092986780891297186551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6853457315707855062915401 5140092986780891297186551)
          ·
            refine ⟨7710139480171336945779827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5140092986780891297186551 7710139480171336945779827)
            ·
              refine ⟨11565209220257005418669741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7710139480171336945779827 11565209220257005418669741)
              ·
                refine ⟨4336953457596377032001153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11565209220257005418669741 4336953457596377032001153)
                ·
                  refine ⟨3252715093197282774000865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4336953457596377032001153 3252715093197282774000865)
                  ·
                    refine ⟨2439536319897962080500649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3252715093197282774000865 2439536319897962080500649)
                    ·
                      refine ⟨1829652239923471560375487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2439536319897962080500649 1829652239923471560375487)
                      ·
                        rfl

theorem cell23_3563235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_3563235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3563235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3563235 prefixEnd_3563235 := by exact prefixLift 3563235
  have htrace : WordTrace (prefixWord ++ tailWord_3563235) baseStart_3563235 baseEnd_3563235 := by
    simpa [prefixWord, tailWord_3563235, baseEnd_3563235] using wordTrace_append hprefix tailTrace_3563235
  have hstable : (prefixWord ++ tailWord_3563235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563235).length < 2 ^ (prefixWord ++ tailWord_3563235).sum := by decide
  have hdescent : baseEnd_3563235 < baseStart_3563235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563247 : List Nat := [1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 7]
def baseStart_3563247 : Nat := 118140960795 + 3563247 * 2 ^ 59
def prefixEnd_3563247 : Nat := 4983230072969 + 3 ^ 40 * 3563247 * 2
def baseEnd_3563247 : Nat := 1829658401691325513425431

theorem tailTrace_3563247 : CollatzResearch.WordTrace tailWord_3563247 prefixEnd_3563247 1829658401691325513425431 := by
  unfold tailWord_3563247
  simp only [CollatzResearch.WordTrace]
  refine ⟨129962294921972147983239995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86641529947981431988826663 129962294921972147983239995)
  ·
    refine ⟨194943442382958221974859993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129962294921972147983239995 194943442382958221974859993)
    ·
      refine ⟨146207581787218666481144995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194943442382958221974859993 146207581787218666481144995)
      ·
        refine ⟨219311372680827999721717493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146207581787218666481144995 219311372680827999721717493)
        ·
          refine ⟨20560441188827624973911015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 219311372680827999721717493 20560441188827624973911015)
          ·
            refine ⟨30840661783241437460866523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20560441188827624973911015 30840661783241437460866523)
            ·
              refine ⟨46260992674862156191299785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30840661783241437460866523 46260992674862156191299785)
              ·
                refine ⟨34695744506146617143474839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46260992674862156191299785 34695744506146617143474839)
                ·
                  refine ⟨52043616759219925715212259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34695744506146617143474839 52043616759219925715212259)
                  ·
                    refine ⟨78065425138829888572818389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52043616759219925715212259 78065425138829888572818389)
                    ·
                      refine ⟨1829658401691325513425431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 78065425138829888572818389 1829658401691325513425431)
                      ·
                        rfl

theorem cell23_3563247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 7].length) (baseStart_3563247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3563247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3563247 prefixEnd_3563247 := by exact prefixLift 3563247
  have htrace : WordTrace (prefixWord ++ tailWord_3563247) baseStart_3563247 baseEnd_3563247 := by
    simpa [prefixWord, tailWord_3563247, baseEnd_3563247] using wordTrace_append hprefix tailTrace_3563247
  have hstable : (prefixWord ++ tailWord_3563247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563247).length < 2 ^ (prefixWord ++ tailWord_3563247).sum := by decide
  have hdescent : baseEnd_3563247 < baseStart_3563247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563301 : List Nat := [1, 3, 1, 2, 3, 3, 1, 2, 3, 4]
def baseStart_3563301 : Nat := 118140960795 + 3563301 * 2 ^ 59
def prefixEnd_3563301 : Nat := 4983230072969 + 3 ^ 40 * 3563301 * 2
def baseEnd_3563301 : Nat := 609895376548889434050061

theorem tailTrace_3563301 : CollatzResearch.WordTrace tailWord_3563301 prefixEnd_3563301 609895376548889434050061 := by
  unfold tailWord_3563301
  simp only [CollatzResearch.WordTrace]
  refine ⟨129964264463776515205705757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86642842975851010137137171 129964264463776515205705757)
  ·
    refine ⟨48736599173916193202139659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129964264463776515205705757 48736599173916193202139659)
    ·
      refine ⟨73104898760874289803209489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48736599173916193202139659 73104898760874289803209489)
      ·
        refine ⟨54828674070655717352407117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73104898760874289803209489 54828674070655717352407117)
        ·
          refine ⟨20560752776495894007152669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54828674070655717352407117 20560752776495894007152669)
          ·
            refine ⟨7710282291185960252682251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20560752776495894007152669 7710282291185960252682251)
            ·
              refine ⟨11565423436778940379023377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7710282291185960252682251 11565423436778940379023377)
              ·
                refine ⟨8674067577584205284267533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11565423436778940379023377 8674067577584205284267533)
                ·
                  refine ⟨3252775341594076981600325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8674067577584205284267533 3252775341594076981600325)
                  ·
                    refine ⟨609895376548889434050061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3252775341594076981600325 609895376548889434050061)
                    ·
                      rfl

theorem cell23_3563301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 2, 3, 4].length) (baseStart_3563301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3563301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3563301 prefixEnd_3563301 := by exact prefixLift 3563301
  have htrace : WordTrace (prefixWord ++ tailWord_3563301) baseStart_3563301 baseEnd_3563301 := by
    simpa [prefixWord, tailWord_3563301, baseEnd_3563301] using wordTrace_append hprefix tailTrace_3563301
  have hstable : (prefixWord ++ tailWord_3563301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563301).length < 2 ^ (prefixWord ++ tailWord_3563301).sum := by decide
  have hdescent : baseEnd_3563301 < baseStart_3563301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563331 : List Nat := [1, 1, 1, 3, 1, 7, 1, 2, 6]
def baseStart_3563331 : Nat := 118140960795 + 3563331 * 2 ^ 59
def prefixEnd_3563331 : Nat := 4983230072969 + 3 ^ 40 * 3563331 * 2
def baseEnd_3563331 : Nat := 203300170451811464975005

theorem tailTrace_3563331 : CollatzResearch.WordTrace tailWord_3563331 prefixEnd_3563331 203300170451811464975005 := by
  unfold tailWord_3563331
  simp only [CollatzResearch.WordTrace]
  refine ⟨129965358653667830329297847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86643572435778553552865231 129965358653667830329297847)
  ·
    refine ⟨194948037980501745493946771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129965358653667830329297847 194948037980501745493946771)
    ·
      refine ⟨292422056970752618240920157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194948037980501745493946771 292422056970752618240920157)
      ·
        refine ⟨109658271364032231840345059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 292422056970752618240920157 109658271364032231840345059)
        ·
          refine ⟨164487407046048347760517589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109658271364032231840345059 164487407046048347760517589)
          ·
            refine ⟨3855173602641758150637131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 164487407046048347760517589 3855173602641758150637131)
            ·
              refine ⟨5782760403962637225955697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3855173602641758150637131 5782760403962637225955697)
              ·
                refine ⟨4337070302971977919466773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5782760403962637225955697 4337070302971977919466773)
                ·
                  refine ⟨203300170451811464975005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4337070302971977919466773 203300170451811464975005)
                  ·
                    rfl

theorem cell23_3563331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 2, 6].length) (baseStart_3563331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3563331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3563331 prefixEnd_3563331 := by exact prefixLift 3563331
  have htrace : WordTrace (prefixWord ++ tailWord_3563331) baseStart_3563331 baseEnd_3563331 := by
    simpa [prefixWord, tailWord_3563331, baseEnd_3563331] using wordTrace_append hprefix tailTrace_3563331
  have hstable : (prefixWord ++ tailWord_3563331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563331).length < 2 ^ (prefixWord ++ tailWord_3563331).sum := by decide
  have hdescent : baseEnd_3563331 < baseStart_3563331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563348 : List Nat := [2, 4, 1, 1, 3, 2, 3, 1, 6]
def baseStart_3563348 : Nat := 118140960795 + 3563348 * 2 ^ 59
def prefixEnd_3563348 : Nat := 4983230072969 + 3 ^ 40 * 3563348 * 2
def baseEnd_3563348 : Nat := 203301140359714402029163

theorem tailTrace_3563348 : CollatzResearch.WordTrace tailWord_3563348 prefixEnd_3563348 203301140359714402029163 := by
  unfold tailWord_3563348
  simp only [CollatzResearch.WordTrace]
  refine ⟨64982989347303121116333349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86643985796404161488444465 64982989347303121116333349)
  ·
    refine ⟨12184310502619335209312503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64982989347303121116333349 12184310502619335209312503)
    ·
      refine ⟨18276465753929002813968755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12184310502619335209312503 18276465753929002813968755)
      ·
        refine ⟨27414698630893504220953133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18276465753929002813968755 27414698630893504220953133)
        ·
          refine ⟨10280511986585064082857425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27414698630893504220953133 10280511986585064082857425)
          ·
            refine ⟨7710383989938798062143069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10280511986585064082857425 7710383989938798062143069)
            ·
              refine ⟨2891393996227049273303651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7710383989938798062143069 2891393996227049273303651)
              ·
                refine ⟨4337090994340573909955477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2891393996227049273303651 4337090994340573909955477)
                ·
                  refine ⟨203301140359714402029163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4337090994340573909955477 203301140359714402029163)
                  ·
                    rfl

theorem cell23_3563348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 1, 6].length) (baseStart_3563348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3563348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3563348 prefixEnd_3563348 := by exact prefixLift 3563348
  have htrace : WordTrace (prefixWord ++ tailWord_3563348) baseStart_3563348 baseEnd_3563348 := by
    simpa [prefixWord, tailWord_3563348, baseEnd_3563348] using wordTrace_append hprefix tailTrace_3563348
  have hstable : (prefixWord ++ tailWord_3563348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563348).length < 2 ^ (prefixWord ++ tailWord_3563348).sum := by decide
  have hdescent : baseEnd_3563348 < baseStart_3563348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563361 : List Nat := [1, 2, 3, 1, 1, 1, 6, 2, 1, 5]
def baseStart_3563361 : Nat := 118140960795 + 3563361 * 2 ^ 59
def prefixEnd_3563361 : Nat := 4983230072969 + 3 ^ 40 * 3563361 * 2
def baseEnd_3563361 : Nat := 609905646161979355799969

theorem tailTrace_3563361 : CollatzResearch.WordTrace tailWord_3563361 prefixEnd_3563361 609905646161979355799969 := by
  unfold tailWord_3563361
  simp only [CollatzResearch.WordTrace]
  refine ⟨129966452843559145452889937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86644301895706096968593291 129966452843559145452889937)
  ·
    refine ⟨97474839632669359089667453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129966452843559145452889937 97474839632669359089667453)
    ·
      refine ⟨36553064862251009658625295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97474839632669359089667453 36553064862251009658625295)
      ·
        refine ⟨54829597293376514487937943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36553064862251009658625295 54829597293376514487937943)
        ·
          refine ⟨82244395940064771731906915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54829597293376514487937943 82244395940064771731906915)
          ·
            refine ⟨123366593910097157597860373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82244395940064771731906915 123366593910097157597860373)
            ·
              refine ⟨5782809089535804262399705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 123366593910097157597860373 5782809089535804262399705)
              ·
                refine ⟨4337106817151853196799779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5782809089535804262399705 4337106817151853196799779)
                ·
                  refine ⟨6505660225727779795199669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4337106817151853196799779 6505660225727779795199669)
                  ·
                    refine ⟨609905646161979355799969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6505660225727779795199669 609905646161979355799969)
                    ·
                      rfl

theorem cell23_3563361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 2, 1, 5].length) (baseStart_3563361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3563361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3563361 prefixEnd_3563361 := by exact prefixLift 3563361
  have htrace : WordTrace (prefixWord ++ tailWord_3563361) baseStart_3563361 baseEnd_3563361 := by
    simpa [prefixWord, tailWord_3563361, baseEnd_3563361] using wordTrace_append hprefix tailTrace_3563361
  have hstable : (prefixWord ++ tailWord_3563361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563361).length < 2 ^ (prefixWord ++ tailWord_3563361).sum := by decide
  have hdescent : baseEnd_3563361 < baseStart_3563361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563368 : List Nat := [2, 1, 4, 2, 1, 1, 2, 3, 2, 3, 2]
def baseStart_3563368 : Nat := 118140960795 + 3563368 * 2 ^ 59
def prefixEnd_3563368 : Nat := 4983230072969 + 3 ^ 40 * 3563368 * 2
def baseEnd_3563368 : Nat := 1829720532850519540012375

theorem tailTrace_3563368 : CollatzResearch.WordTrace tailWord_3563368 prefixEnd_3563368 1829720532850519540012375 := by
  unfold tailWord_3563368
  simp only [CollatzResearch.WordTrace]
  refine ⟨64983354077266892824197379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86644472103022523765596505 64983354077266892824197379)
  ·
    refine ⟨97475031115900339236296069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64983354077266892824197379 97475031115900339236296069)
    ·
      refine ⟨18276568334231313606805513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97475031115900339236296069 18276568334231313606805513)
      ·
        refine ⟨13707426250673485205104135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18276568334231313606805513 13707426250673485205104135)
        ·
          refine ⟨20561139376010227807656203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13707426250673485205104135 20561139376010227807656203)
          ·
            refine ⟨30841709064015341711484305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20561139376010227807656203 30841709064015341711484305)
            ·
              refine ⟨23131281798011506283613229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30841709064015341711484305 23131281798011506283613229)
              ·
                refine ⟨8674230674254314856354961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23131281798011506283613229 8674230674254314856354961)
                ·
                  refine ⟨6505673005690736142266221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8674230674254314856354961 6505673005690736142266221)
                  ·
                    refine ⟨2439627377134026053349833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6505673005690736142266221 2439627377134026053349833)
                    ·
                      refine ⟨1829720532850519540012375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2439627377134026053349833 1829720532850519540012375)
                      ·
                        rfl

theorem cell23_3563368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_3563368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3563368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3563368 prefixEnd_3563368 := by exact prefixLift 3563368
  have htrace : WordTrace (prefixWord ++ tailWord_3563368) baseStart_3563368 baseEnd_3563368 := by
    simpa [prefixWord, tailWord_3563368, baseEnd_3563368] using wordTrace_append hprefix tailTrace_3563368
  have hstable : (prefixWord ++ tailWord_3563368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563368).length < 2 ^ (prefixWord ++ tailWord_3563368).sum := by decide
  have hdescent : baseEnd_3563368 < baseStart_3563368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563384 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 1, 8, 3]
def baseStart_3563384 : Nat := 118140960795 + 3563384 * 2 ^ 59
def prefixEnd_3563384 : Nat := 4983230072969 + 3 ^ 40 * 3563384 * 2
def baseEnd_3563384 : Nat := 1829728748540991477412301

theorem tailTrace_3563384 : CollatzResearch.WordTrace tailWord_3563384 prefixEnd_3563384 1829728748540991477412301 := by
  unfold tailWord_3563384
  simp only [CollatzResearch.WordTrace]
  refine ⟨64983645861237910190488603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86644861148317213587318137 64983645861237910190488603)
  ·
    refine ⟨97475468791856865285732905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64983645861237910190488603 97475468791856865285732905)
    ·
      refine ⟨73106601593892648964299679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97475468791856865285732905 73106601593892648964299679)
      ·
        refine ⟨109659902390838973446449519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73106601593892648964299679 109659902390838973446449519)
        ·
          refine ⟨164489853586258460169674279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109659902390838973446449519 164489853586258460169674279)
          ·
            refine ⟨246734780379387690254511419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164489853586258460169674279 246734780379387690254511419)
            ·
              refine ⟨370102170569081535381767129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246734780379387690254511419 370102170569081535381767129)
              ·
                refine ⟨277576627926811151536325347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 370102170569081535381767129 277576627926811151536325347)
                ·
                  refine ⟨416364941890216727304488021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 277576627926811151536325347 416364941890216727304488021)
                  ·
                    refine ⟨4879276662775977273099469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 416364941890216727304488021 4879276662775977273099469)
                    ·
                      refine ⟨1829728748540991477412301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4879276662775977273099469 1829728748540991477412301)
                      ·
                        rfl

theorem cell23_3563384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 1, 8, 3].length) (baseStart_3563384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3563384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3563384 prefixEnd_3563384 := by exact prefixLift 3563384
  have htrace : WordTrace (prefixWord ++ tailWord_3563384) baseStart_3563384 baseEnd_3563384 := by
    simpa [prefixWord, tailWord_3563384, baseEnd_3563384] using wordTrace_append hprefix tailTrace_3563384
  have hstable : (prefixWord ++ tailWord_3563384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563384).length < 2 ^ (prefixWord ++ tailWord_3563384).sum := by decide
  have hdescent : baseEnd_3563384 < baseStart_3563384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563391 : List Nat := [1, 1, 2, 2, 1, 1, 3, 6, 2, 4]
def baseStart_3563391 : Nat := 118140960795 + 3563391 * 2 ^ 59
def prefixEnd_3563391 : Nat := 4983230072969 + 3 ^ 40 * 3563391 * 2
def baseEnd_3563391 : Nat := 609910780968524316674923

theorem tailTrace_3563391 : CollatzResearch.WordTrace tailWord_3563391 prefixEnd_3563391 609910780968524316674923 := by
  unfold tailWord_3563391
  simp only [CollatzResearch.WordTrace]
  refine ⟨129967547033450460576482027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86645031355633640384321351 129967547033450460576482027)
  ·
    refine ⟨194951320550175690864723041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129967547033450460576482027 194951320550175690864723041)
    ·
      refine ⟨146213490412631768148542281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194951320550175690864723041 146213490412631768148542281)
      ·
        refine ⟨109660117809473826111406711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146213490412631768148542281 109660117809473826111406711)
        ·
          refine ⟨164490176714210739167110067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109660117809473826111406711 164490176714210739167110067)
          ·
            refine ⟨246735265071316108750665101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164490176714210739167110067 246735265071316108750665101)
            ·
              refine ⟨92525724401743540781499413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 246735265071316108750665101 92525724401743540781499413)
              ·
                refine ⟨4337143331331728474132785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 92525724401743540781499413 4337143331331728474132785)
                ·
                  refine ⟨3252857498498796355599589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4337143331331728474132785 3252857498498796355599589)
                  ·
                    refine ⟨609910780968524316674923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3252857498498796355599589 609910780968524316674923)
                    ·
                      rfl

theorem cell23_3563391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 6, 2, 4].length) (baseStart_3563391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3563391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3563391 prefixEnd_3563391 := by exact prefixLift 3563391
  have htrace : WordTrace (prefixWord ++ tailWord_3563391) baseStart_3563391 baseEnd_3563391 := by
    simpa [prefixWord, tailWord_3563391, baseEnd_3563391] using wordTrace_append hprefix tailTrace_3563391
  have hstable : (prefixWord ++ tailWord_3563391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563391).length < 2 ^ (prefixWord ++ tailWord_3563391).sum := by decide
  have hdescent : baseEnd_3563391 < baseStart_3563391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563401 : List Nat := [1, 2, 1, 1, 5, 1, 2, 2, 3, 2, 3]
def baseStart_3563401 : Nat := 118140960795 + 3563401 * 2 ^ 59
def prefixEnd_3563401 : Nat := 4983230072969 + 3 ^ 40 * 3563401 * 2
def baseEnd_3563401 : Nat := 1829737477712117910899723

theorem tailTrace_3563401 : CollatzResearch.WordTrace tailWord_3563401 prefixEnd_3563401 1829737477712117910899723 := by
  unfold tailWord_3563401
  simp only [CollatzResearch.WordTrace]
  refine ⟨129967911763414232284346057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86645274508942821522897371 129967911763414232284346057)
  ·
    refine ⟨97475933822560674213259543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129967911763414232284346057 97475933822560674213259543)
    ·
      refine ⟨146213900733841011319889315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97475933822560674213259543 146213900733841011319889315)
      ·
        refine ⟨219320851100761516979833973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146213900733841011319889315 219320851100761516979833973)
        ·
          refine ⟨20561329790696392216859435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 219320851100761516979833973 20561329790696392216859435)
          ·
            refine ⟨30841994686044588325289153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20561329790696392216859435 30841994686044588325289153)
            ·
              refine ⟨23131496014533441243966865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30841994686044588325289153 23131496014533441243966865)
              ·
                refine ⟨17348622010900080932975149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23131496014533441243966865 17348622010900080932975149)
                ·
                  refine ⟨6505733254087530349865681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17348622010900080932975149 6505733254087530349865681)
                  ·
                    refine ⟨4879299940565647762399261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6505733254087530349865681 4879299940565647762399261)
                    ·
                      refine ⟨1829737477712117910899723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4879299940565647762399261 1829737477712117910899723)
                      ·
                        rfl

theorem cell23_3563401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 3, 2, 3].length) (baseStart_3563401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3563401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3563401 prefixEnd_3563401 := by exact prefixLift 3563401
  have htrace : WordTrace (prefixWord ++ tailWord_3563401) baseStart_3563401 baseEnd_3563401 := by
    simpa [prefixWord, tailWord_3563401, baseEnd_3563401] using wordTrace_append hprefix tailTrace_3563401
  have hstable : (prefixWord ++ tailWord_3563401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563401).length < 2 ^ (prefixWord ++ tailWord_3563401).sum := by decide
  have hdescent : baseEnd_3563401 < baseStart_3563401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563418 : List Nat := [3, 1, 1, 4, 2, 2, 1, 1, 3, 2, 3]
def baseStart_3563418 : Nat := 118140960795 + 3563418 * 2 ^ 59
def prefixEnd_3563418 : Nat := 4983230072969 + 3 ^ 40 * 3563418 * 2
def baseEnd_3563418 : Nat := 1829746206883244344387145

theorem tailTrace_3563418 : CollatzResearch.WordTrace tailWord_3563418 prefixEnd_3563418 1829746206883244344387145 := by
  unfold tailWord_3563418
  simp only [CollatzResearch.WordTrace]
  refine ⟨32492132951088161046928727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86645687869568429458476605 32492132951088161046928727)
  ·
    refine ⟨48738199426632241570393091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32492132951088161046928727 48738199426632241570393091)
    ·
      refine ⟨73107299139948362355589637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48738199426632241570393091 73107299139948362355589637)
      ·
        refine ⟨13707618588740317941673057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73107299139948362355589637 13707618588740317941673057)
        ·
          refine ⟨10280713941555238456254793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13707618588740317941673057 10280713941555238456254793)
          ·
            refine ⟨7710535456166428842191095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10280713941555238456254793 7710535456166428842191095)
            ·
              refine ⟨11565803184249643263286643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7710535456166428842191095 11565803184249643263286643)
              ·
                refine ⟨17348704776374464894929965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11565803184249643263286643 17348704776374464894929965)
                ·
                  refine ⟨6505764291140424335598737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17348704776374464894929965 6505764291140424335598737)
                  ·
                    refine ⟨4879323218355318251699053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6505764291140424335598737 4879323218355318251699053)
                    ·
                      refine ⟨1829746206883244344387145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4879323218355318251699053 1829746206883244344387145)
                      ·
                        rfl

theorem cell23_3563418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_3563418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3563418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3563418 prefixEnd_3563418 := by exact prefixLift 3563418
  have htrace : WordTrace (prefixWord ++ tailWord_3563418) baseStart_3563418 baseEnd_3563418 := by
    simpa [prefixWord, tailWord_3563418, baseEnd_3563418] using wordTrace_append hprefix tailTrace_3563418
  have hstable : (prefixWord ++ tailWord_3563418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563418).length < 2 ^ (prefixWord ++ tailWord_3563418).sum := by decide
  have hdescent : baseEnd_3563418 < baseStart_3563418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563438 : List Nat := [4, 1, 5, 1, 12]
def baseStart_3563438 : Nat := 118140960795 + 3563438 * 2 ^ 59
def prefixEnd_3563438 : Nat := 4983230072969 + 3 ^ 40 * 3563438 * 2
def baseEnd_3563438 : Nat := 2509954014398263739557

theorem tailTrace_3563438 : CollatzResearch.WordTrace tailWord_3563438 prefixEnd_3563438 2509954014398263739557 := by
  unfold tailWord_3563438
  simp only [CollatzResearch.WordTrace]
  refine ⟨16246157658035023450430371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86646174176186791735628645 16246157658035023450430371)
  ·
    refine ⟨24369236487052535175645557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16246157658035023450430371 24369236487052535175645557)
    ·
      refine ⟨2284615920661175172716771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24369236487052535175645557 2284615920661175172716771)
      ·
        refine ⟨3426923880991762759075157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2284615920661175172716771 3426923880991762759075157)
        ·
          refine ⟨2509954014398263739557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 3426923880991762759075157 2509954014398263739557)
          ·
            rfl

theorem cell23_3563438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 12].length) (baseStart_3563438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3563438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3563438 prefixEnd_3563438 := by exact prefixLift 3563438
  have htrace : WordTrace (prefixWord ++ tailWord_3563438) baseStart_3563438 baseEnd_3563438 := by
    simpa [prefixWord, tailWord_3563438, baseEnd_3563438] using wordTrace_append hprefix tailTrace_3563438
  have hstable : (prefixWord ++ tailWord_3563438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563438).length < 2 ^ (prefixWord ++ tailWord_3563438).sum := by decide
  have hdescent : baseEnd_3563438 < baseStart_3563438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563551 : List Nat := [1, 1, 2, 4, 1, 2, 2, 2, 1, 2, 5]
def baseStart_3563551 : Nat := 118140960795 + 3563551 * 2 ^ 59
def prefixEnd_3563551 : Nat := 4983230072969 + 3 ^ 40 * 3563551 * 2
def baseEnd_3563551 : Nat := 1829814499810292324024033

theorem tailTrace_3563551 : CollatzResearch.WordTrace tailWord_3563551 prefixEnd_3563551 1829814499810292324024033 := by
  unfold tailWord_3563551
  simp only [CollatzResearch.WordTrace]
  refine ⟨129973382712870807902306507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86648921808580538601537671 129973382712870807902306507)
  ·
    refine ⟨194960074069306211853459761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129973382712870807902306507 194960074069306211853459761)
    ·
      refine ⟨146220055551979658890094821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194960074069306211853459761 146220055551979658890094821)
      ·
        refine ⟨27416260415996186041892779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146220055551979658890094821 27416260415996186041892779)
        ·
          refine ⟨41124390623994279062839169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27416260415996186041892779 41124390623994279062839169)
          ·
            refine ⟨30843292967995709297129377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41124390623994279062839169 30843292967995709297129377)
            ·
              refine ⟨23132469725996781972847033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30843292967995709297129377 23132469725996781972847033)
              ·
                refine ⟨17349352294497586479635275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23132469725996781972847033 17349352294497586479635275)
                ·
                  refine ⟨26024028441746379719452913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17349352294497586479635275 26024028441746379719452913)
                  ·
                    refine ⟨19518021331309784789589685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26024028441746379719452913 19518021331309784789589685)
                    ·
                      refine ⟨1829814499810292324024033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19518021331309784789589685 1829814499810292324024033)
                      ·
                        rfl

theorem cell23_3563551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_3563551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3563551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3563551 prefixEnd_3563551 := by exact prefixLift 3563551
  have htrace : WordTrace (prefixWord ++ tailWord_3563551) baseStart_3563551 baseEnd_3563551 := by
    simpa [prefixWord, tailWord_3563551, baseEnd_3563551] using wordTrace_append hprefix tailTrace_3563551
  have hstable : (prefixWord ++ tailWord_3563551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563551).length < 2 ^ (prefixWord ++ tailWord_3563551).sum := by decide
  have hdescent : baseEnd_3563551 < baseStart_3563551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563562 : List Nat := [3, 1, 4, 1, 2, 2, 3, 2, 5]
def baseStart_3563562 : Nat := 118140960795 + 3563562 * 2 ^ 59
def prefixEnd_3563562 : Nat := 4983230072969 + 3 ^ 40 * 3563562 * 2
def baseEnd_3563562 : Nat := 203313349788610197887387

theorem tailTrace_3563562 : CollatzResearch.WordTrace tailWord_3563562 prefixEnd_3563562 203313349788610197887387 := by
  unfold tailWord_3563562
  simp only [CollatzResearch.WordTrace]
  refine ⟨32493445978957739195239235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86649189277220637853971293 32493445978957739195239235)
  ·
    refine ⟨48740168968436608792858853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32493445978957739195239235 48740168968436608792858853)
    ·
      refine ⟨9138781681581864148661035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48740168968436608792858853 9138781681581864148661035)
      ·
        refine ⟨13708172522372796222991553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9138781681581864148661035 13708172522372796222991553)
        ·
          refine ⟨10281129391779597167243665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13708172522372796222991553 10281129391779597167243665)
          ·
            refine ⟨7710847043834697875432749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10281129391779597167243665 7710847043834697875432749)
            ·
              refine ⟨2891567641438011703287281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7710847043834697875432749 2891567641438011703287281)
              ·
                refine ⟨2168675731078508777465461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2891567641438011703287281 2168675731078508777465461)
                ·
                  refine ⟨203313349788610197887387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2168675731078508777465461 203313349788610197887387)
                  ·
                    rfl

theorem cell23_3563562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 2, 5].length) (baseStart_3563562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3563562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3563562 prefixEnd_3563562 := by exact prefixLift 3563562
  have htrace : WordTrace (prefixWord ++ tailWord_3563562) baseStart_3563562 baseEnd_3563562 := by
    simpa [prefixWord, tailWord_3563562, baseEnd_3563562] using wordTrace_append hprefix tailTrace_3563562
  have hstable : (prefixWord ++ tailWord_3563562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563562).length < 2 ^ (prefixWord ++ tailWord_3563562).sum := by decide
  have hdescent : baseEnd_3563562 < baseStart_3563562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563578 : List Nat := [3, 1, 1, 1, 3, 1, 1, 3, 1, 6, 2]
def baseStart_3563578 : Nat := 118140960795 + 3563578 * 2 ^ 59
def prefixEnd_3563578 : Nat := 4983230072969 + 3 ^ 40 * 3563578 * 2
def baseEnd_3563578 : Nat := 1829828363787963718386409

theorem tailTrace_3563578 : CollatzResearch.WordTrace tailWord_3563578 prefixEnd_3563578 1829828363787963718386409 := by
  unfold tailWord_3563578
  simp only [CollatzResearch.WordTrace]
  refine ⟨32493591870943247878384847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86649578322515327675692925 32493591870943247878384847)
  ·
    refine ⟨48740387806414871817577271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32493591870943247878384847 48740387806414871817577271)
    ·
      refine ⟨73110581709622307726365907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48740387806414871817577271 73110581709622307726365907)
      ·
        refine ⟨109665872564433461589548861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73110581709622307726365907 109665872564433461589548861)
        ·
          refine ⟨41124702211662548096080823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109665872564433461589548861 41124702211662548096080823)
          ·
            refine ⟨61687053317493822144121235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41124702211662548096080823 61687053317493822144121235)
            ·
              refine ⟨92530579976240733216181853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61687053317493822144121235 92530579976240733216181853)
              ·
                refine ⟨34698967491090274956068195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92530579976240733216181853 34698967491090274956068195)
                ·
                  refine ⟨52048451236635412434102293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34698967491090274956068195 52048451236635412434102293)
                  ·
                    refine ⟨2439771151717284957848545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 52048451236635412434102293 2439771151717284957848545)
                    ·
                      refine ⟨1829828363787963718386409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2439771151717284957848545 1829828363787963718386409)
                      ·
                        rfl

theorem cell23_3563578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 1, 6, 2].length) (baseStart_3563578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3563578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3563578 prefixEnd_3563578 := by exact prefixLift 3563578
  have htrace : WordTrace (prefixWord ++ tailWord_3563578) baseStart_3563578 baseEnd_3563578 := by
    simpa [prefixWord, tailWord_3563578, baseEnd_3563578] using wordTrace_append hprefix tailTrace_3563578
  have hstable : (prefixWord ++ tailWord_3563578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563578).length < 2 ^ (prefixWord ++ tailWord_3563578).sum := by decide
  have hdescent : baseEnd_3563578 < baseStart_3563578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563645 : List Nat := [1, 4, 1, 1, 3, 2, 1, 1, 5, 1, 3]
def baseStart_3563645 : Nat := 118140960795 + 3563645 * 2 ^ 59
def prefixEnd_3563645 : Nat := 4983230072969 + 3 ^ 40 * 3563645 * 2
def baseEnd_3563645 : Nat := 1829862766991814956248601

theorem tailTrace_3563645 : CollatzResearch.WordTrace tailWord_3563645 prefixEnd_3563645 1829862766991814956248601 := by
  unfold tailWord_3563645
  simp only [CollatzResearch.WordTrace]
  refine ⟨129976811174530261956228389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86651207449686841304152259 129976811174530261956228389)
  ·
    refine ⟨24370652095224424116792823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129976811174530261956228389 24370652095224424116792823)
    ·
      refine ⟨36555978142836636175189235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24370652095224424116792823 36555978142836636175189235)
      ·
        refine ⟨54833967214254954262783853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36555978142836636175189235 54833967214254954262783853)
        ·
          refine ⟨20562737705345607848543945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54833967214254954262783853 20562737705345607848543945)
          ·
            refine ⟨15422053279009205886407959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20562737705345607848543945 15422053279009205886407959)
            ·
              refine ⟨23133079918513808829611939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15422053279009205886407959 23133079918513808829611939)
              ·
                refine ⟨34699619877770713244417909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23133079918513808829611939 34699619877770713244417909)
                ·
                  refine ⟨3253089363541004366664179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34699619877770713244417909 3253089363541004366664179)
                  ·
                    refine ⟨4879634045311506549996269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3253089363541004366664179 4879634045311506549996269)
                    ·
                      refine ⟨1829862766991814956248601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4879634045311506549996269 1829862766991814956248601)
                      ·
                        rfl

theorem cell23_3563645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 5, 1, 3].length) (baseStart_3563645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3563645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3563645 prefixEnd_3563645 := by exact prefixLift 3563645
  have htrace : WordTrace (prefixWord ++ tailWord_3563645) baseStart_3563645 baseEnd_3563645 := by
    simpa [prefixWord, tailWord_3563645, baseEnd_3563645] using wordTrace_append hprefix tailTrace_3563645
  have hstable : (prefixWord ++ tailWord_3563645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563645).length < 2 ^ (prefixWord ++ tailWord_3563645).sum := by decide
  have hdescent : baseEnd_3563645 < baseStart_3563645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563648 : List Nat := [2, 1, 1, 2, 1, 3, 1, 6, 1, 5]
def baseStart_3563648 : Nat := 118140960795 + 3563648 * 2 ^ 59
def prefixEnd_3563648 : Nat := 4983230072969 + 3 ^ 40 * 3563648 * 2
def baseEnd_3563648 : Nat := 609954769144592814837029

theorem tailTrace_3563648 : CollatzResearch.WordTrace tailWord_3563648 prefixEnd_3563648 609954769144592814837029 := by
  unfold tailWord_3563648
  simp only [CollatzResearch.WordTrace]
  refine ⟨64988460296759696734293799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86651280395679595645725065 64988460296759696734293799)
  ·
    refine ⟨97482690445139545101440699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64988460296759696734293799 97482690445139545101440699)
    ·
      refine ⟨146224035667709317652161049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97482690445139545101440699 146224035667709317652161049)
      ·
        refine ⟨109668026750781988239120787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146224035667709317652161049 109668026750781988239120787)
        ·
          refine ⟨164502040126172982358681181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109668026750781988239120787 164502040126172982358681181)
          ·
            refine ⟨61688265047314868384505443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164502040126172982358681181 61688265047314868384505443)
            ·
              refine ⟨92532397570972302576758165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61688265047314868384505443 92532397570972302576758165)
              ·
                refine ⟨4337456136139326683285539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 92532397570972302576758165 4337456136139326683285539)
                ·
                  refine ⟨6506184204208990024928309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4337456136139326683285539 6506184204208990024928309)
                  ·
                    refine ⟨609954769144592814837029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6506184204208990024928309 609954769144592814837029)
                    ·
                      rfl

theorem cell23_3563648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 6, 1, 5].length) (baseStart_3563648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3563648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3563648 prefixEnd_3563648 := by exact prefixLift 3563648
  have htrace : WordTrace (prefixWord ++ tailWord_3563648) baseStart_3563648 baseEnd_3563648 := by
    simpa [prefixWord, tailWord_3563648, baseEnd_3563648] using wordTrace_append hprefix tailTrace_3563648
  have hstable : (prefixWord ++ tailWord_3563648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563648).length < 2 ^ (prefixWord ++ tailWord_3563648).sum := by decide
  have hdescent : baseEnd_3563648 < baseStart_3563648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563649 : List Nat := [1, 2, 4, 2, 4, 1, 1, 1, 2, 2, 3]
def baseStart_3563649 : Nat := 118140960795 + 3563649 * 2 ^ 59
def prefixEnd_3563649 : Nat := 4983230072969 + 3 ^ 40 * 3563649 * 2
def baseEnd_3563649 : Nat := 1829864820914432940598583

theorem tailTrace_3563649 : CollatzResearch.WordTrace tailWord_3563649 prefixEnd_3563649 1829864820914432940598583 := by
  unfold tailWord_3563649
  simp only [CollatzResearch.WordTrace]
  refine ⟨129976957066515770639374001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86651304711010513759582667 129976957066515770639374001)
  ·
    refine ⟨97482717799886827979530501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129976957066515770639374001 97482717799886827979530501)
    ·
      refine ⟨18278009587478780246161969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97482717799886827979530501 18278009587478780246161969)
      ·
        refine ⟨13708507190609085184621477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18278009587478780246161969 13708507190609085184621477)
        ·
          refine ⟨2570345098239203472116527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13708507190609085184621477 2570345098239203472116527)
          ·
            refine ⟨3855517647358805208174791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2570345098239203472116527 3855517647358805208174791)
            ·
              refine ⟨5783276471038207812262187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3855517647358805208174791 5783276471038207812262187)
              ·
                refine ⟨8674914706557311718393281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5783276471038207812262187 8674914706557311718393281)
                ·
                  refine ⟨6506186029917983788794961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8674914706557311718393281 6506186029917983788794961)
                  ·
                    refine ⟨4879639522438487841596221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6506186029917983788794961 4879639522438487841596221)
                    ·
                      refine ⟨1829864820914432940598583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4879639522438487841596221 1829864820914432940598583)
                      ·
                        rfl

theorem cell23_3563649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_3563649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3563649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3563649 prefixEnd_3563649 := by exact prefixLift 3563649
  have htrace : WordTrace (prefixWord ++ tailWord_3563649) baseStart_3563649 baseEnd_3563649 := by
    simpa [prefixWord, tailWord_3563649, baseEnd_3563649] using wordTrace_append hprefix tailTrace_3563649
  have hstable : (prefixWord ++ tailWord_3563649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563649).length < 2 ^ (prefixWord ++ tailWord_3563649).sum := by decide
  have hdescent : baseEnd_3563649 < baseStart_3563649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563679 : List Nat := [1, 1, 2, 6, 1, 1, 2, 4, 1, 1, 3]
def baseStart_3563679 : Nat := 118140960795 + 3563679 * 2 ^ 59
def prefixEnd_3563679 : Nat := 4983230072969 + 3 ^ 40 * 3563679 * 2
def baseEnd_3563679 : Nat := 1829880225334067823223445

theorem tailTrace_3563679 : CollatzResearch.WordTrace tailWord_3563679 prefixEnd_3563679 1829880225334067823223445 := by
  unfold tailWord_3563679
  simp only [CollatzResearch.WordTrace]
  refine ⟨129978051256407085762966091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86652034170938057175310727 129978051256407085762966091)
  ·
    refine ⟨194967076884610628644449137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129978051256407085762966091 194967076884610628644449137)
    ·
      refine ⟨146225307663457971483336853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194967076884610628644449137 146225307663457971483336853)
      ·
        refine ⟨6854311296724592413281415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 146225307663457971483336853 6854311296724592413281415)
        ·
          refine ⟨10281466945086888619922123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6854311296724592413281415 10281466945086888619922123)
          ·
            refine ⟨15422200417630332929883185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10281466945086888619922123 15422200417630332929883185)
            ·
              refine ⟨11566650313222749697412389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15422200417630332929883185 11566650313222749697412389)
              ·
                refine ⟨2168746933729265568264823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11566650313222749697412389 2168746933729265568264823)
                ·
                  refine ⟨3253120400593898352397235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2168746933729265568264823 3253120400593898352397235)
                  ·
                    refine ⟨4879680600890847528595853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3253120400593898352397235 4879680600890847528595853)
                    ·
                      refine ⟨1829880225334067823223445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4879680600890847528595853 1829880225334067823223445)
                      ·
                        rfl

theorem cell23_3563679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_3563679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3563679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3563679 prefixEnd_3563679 := by exact prefixLift 3563679
  have htrace : WordTrace (prefixWord ++ tailWord_3563679) baseStart_3563679 baseEnd_3563679 := by
    simpa [prefixWord, tailWord_3563679, baseEnd_3563679] using wordTrace_append hprefix tailTrace_3563679
  have hstable : (prefixWord ++ tailWord_3563679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563679).length < 2 ^ (prefixWord ++ tailWord_3563679).sum := by decide
  have hdescent : baseEnd_3563679 < baseStart_3563679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563698 : List Nat := [3, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6]
def baseStart_3563698 : Nat := 118140960795 + 3563698 * 2 ^ 59
def prefixEnd_3563698 : Nat := 4983230072969 + 3 ^ 40 * 3563698 * 2
def baseEnd_3563698 : Nat := 1829889981466503248885857

theorem tailTrace_3563698 : CollatzResearch.WordTrace tailWord_3563698 prefixEnd_3563698 1829889981466503248885857 := by
  unfold tailWord_3563698
  simp only [CollatzResearch.WordTrace]
  refine ⟨32494686060834563001976937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86652496162225501338605165 32494686060834563001976937)
  ·
    refine ⟨24371014545625922251482703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32494686060834563001976937 24371014545625922251482703)
    ·
      refine ⟨36556521818438883377224055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24371014545625922251482703 36556521818438883377224055)
      ·
        refine ⟨54834782727658325065836083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36556521818438883377224055 54834782727658325065836083)
        ·
          refine ⟨82252174091487487598754125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54834782727658325065836083 82252174091487487598754125)
          ·
            refine ⟨30844565284307807849532797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82252174091487487598754125 30844565284307807849532797)
            ·
              refine ⟨11566711981615427943574799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30844565284307807849532797 11566711981615427943574799)
              ·
                refine ⟨17350067972423141915362199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11566711981615427943574799 17350067972423141915362199)
                ·
                  refine ⟨26025101958634712873043299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17350067972423141915362199 26025101958634712873043299)
                  ·
                    refine ⟨39037652937952069309564949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26025101958634712873043299 39037652937952069309564949)
                    ·
                      refine ⟨1829889981466503248885857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39037652937952069309564949 1829889981466503248885857)
                      ·
                        rfl

theorem cell23_3563698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_3563698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3563698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3563698 prefixEnd_3563698 := by exact prefixLift 3563698
  have htrace : WordTrace (prefixWord ++ tailWord_3563698) baseStart_3563698 baseEnd_3563698 := by
    simpa [prefixWord, tailWord_3563698, baseEnd_3563698] using wordTrace_append hprefix tailTrace_3563698
  have hstable : (prefixWord ++ tailWord_3563698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563698).length < 2 ^ (prefixWord ++ tailWord_3563698).sum := by decide
  have hdescent : baseEnd_3563698 < baseStart_3563698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563713 : List Nat := [1, 2, 6, 1, 2, 2, 1, 3, 1, 1, 3]
def baseStart_3563713 : Nat := 118140960795 + 3563713 * 2 ^ 59
def prefixEnd_3563713 : Nat := 4983230072969 + 3 ^ 40 * 3563713 * 2
def baseEnd_3563713 : Nat := 1829897683676320690198289

theorem tailTrace_3563713 : CollatzResearch.WordTrace tailWord_3563713 prefixEnd_3563713 1829897683676320690198289 := by
  unfold tailWord_3563713
  simp only [CollatzResearch.WordTrace]
  refine ⟨129979291338283909569703793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86652860892189273046469195 129979291338283909569703793)
  ·
    refine ⟨97484468503712932177277845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129979291338283909569703793 97484468503712932177277845)
    ·
      refine ⟨4569584461111543695809899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 97484468503712932177277845 4569584461111543695809899)
      ·
        refine ⟨6854376691667315543714849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4569584461111543695809899 6854376691667315543714849)
        ·
          refine ⟨5140782518750486657786137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6854376691667315543714849 5140782518750486657786137)
          ·
            refine ⟨3855586889062864993339603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5140782518750486657786137 3855586889062864993339603)
            ·
              refine ⟨5783380333594297490009405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3855586889062864993339603 5783380333594297490009405)
              ·
                refine ⟨2168767625097861558753527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5783380333594297490009405 2168767625097861558753527)
                ·
                  refine ⟨3253151437646792338130291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2168767625097861558753527 3253151437646792338130291)
                  ·
                    refine ⟨4879727156470188507195437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3253151437646792338130291 4879727156470188507195437)
                    ·
                      refine ⟨1829897683676320690198289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4879727156470188507195437 1829897683676320690198289)
                      ·
                        rfl

theorem cell23_3563713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_3563713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3563713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3563713 prefixEnd_3563713 := by exact prefixLift 3563713
  have htrace : WordTrace (prefixWord ++ tailWord_3563713) baseStart_3563713 baseEnd_3563713 := by
    simpa [prefixWord, tailWord_3563713, baseEnd_3563713] using wordTrace_append hprefix tailTrace_3563713
  have hstable : (prefixWord ++ tailWord_3563713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563713).length < 2 ^ (prefixWord ++ tailWord_3563713).sum := by decide
  have hdescent : baseEnd_3563713 < baseStart_3563713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563758 : List Nat := [4, 1, 2, 1, 1, 1, 1, 1, 1, 2, 8]
def baseStart_3563758 : Nat := 118140960795 + 3563758 * 2 ^ 59
def prefixEnd_3563758 : Nat := 4983230072969 + 3 ^ 40 * 3563758 * 2
def baseEnd_3563758 : Nat := 1829920790305773014135581

theorem tailTrace_3563758 : CollatzResearch.WordTrace tailWord_3563758 prefixEnd_3563758 1829920790305773014135581 := by
  unfold tailWord_3563758
  simp only [CollatzResearch.WordTrace]
  refine ⟨16247616577890110281886491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86653955082080588170061285 16247616577890110281886491)
  ·
    refine ⟨24371424866835165422829737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16247616577890110281886491 24371424866835165422829737)
    ·
      refine ⟨18278568650126374067122303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24371424866835165422829737 18278568650126374067122303)
      ·
        refine ⟨27417852975189561100683455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18278568650126374067122303 27417852975189561100683455)
        ·
          refine ⟨41126779462784341651025183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27417852975189561100683455 41126779462784341651025183)
          ·
            refine ⟨61690169194176512476537775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41126779462784341651025183 61690169194176512476537775)
            ·
              refine ⟨92535253791264768714806663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61690169194176512476537775 92535253791264768714806663)
              ·
                refine ⟨138802880686897153072209995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92535253791264768714806663 138802880686897153072209995)
                ·
                  refine ⟨208204321030345729608314993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138802880686897153072209995 208204321030345729608314993)
                  ·
                    refine ⟨156153240772759297206236245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 208204321030345729608314993 156153240772759297206236245)
                    ·
                      refine ⟨1829920790305773014135581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 156153240772759297206236245 1829920790305773014135581)
                      ·
                        rfl

theorem cell23_3563758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_3563758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3563758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3563758 prefixEnd_3563758 := by exact prefixLift 3563758
  have htrace : WordTrace (prefixWord ++ tailWord_3563758) baseStart_3563758 baseEnd_3563758 := by
    simpa [prefixWord, tailWord_3563758, baseEnd_3563758] using wordTrace_append hprefix tailTrace_3563758
  have hstable : (prefixWord ++ tailWord_3563758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563758).length < 2 ^ (prefixWord ++ tailWord_3563758).sum := by decide
  have hdescent : baseEnd_3563758 < baseStart_3563758 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563779 : List Nat := [1, 1, 1, 3, 2, 3, 5, 1, 1, 3, 2]
def baseStart_3563779 : Nat := 118140960795 + 3563779 * 2 ^ 59
def prefixEnd_3563779 : Nat := 4983230072969 + 3 ^ 40 * 3563779 * 2
def baseEnd_3563779 : Nat := 1829931573399517431972985

theorem tailTrace_3563779 : CollatzResearch.WordTrace tailWord_3563779 prefixEnd_3563779 1829931573399517431972985 := by
  unfold tailWord_3563779
  simp only [CollatzResearch.WordTrace]
  refine ⟨129981698556044802841606391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86654465704029868561070927 129981698556044802841606391)
  ·
    refine ⟨194972547834067204262409587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129981698556044802841606391 194972547834067204262409587)
    ·
      refine ⟨292458821751100806393614381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194972547834067204262409587 292458821751100806393614381)
      ·
        refine ⟨109672058156662802397605393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 292458821751100806393614381 109672058156662802397605393)
        ·
          refine ⟨82254043617497101798204045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109672058156662802397605393 82254043617497101798204045)
          ·
            refine ⟨30845266356561413174326517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82254043617497101798204045 30845266356561413174326517)
            ·
              refine ⟨2891743720927632485093111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30845266356561413174326517 2891743720927632485093111)
              ·
                refine ⟨4337615581391448727639667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2891743720927632485093111 4337615581391448727639667)
                ·
                  refine ⟨6506423372087173091459501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4337615581391448727639667 6506423372087173091459501)
                  ·
                    refine ⟨2439908764532689909297313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6506423372087173091459501 2439908764532689909297313)
                    ·
                      refine ⟨1829931573399517431972985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2439908764532689909297313 1829931573399517431972985)
                      ·
                        rfl

theorem cell23_3563779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 1, 1, 3, 2].length) (baseStart_3563779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3563779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3563779 prefixEnd_3563779 := by exact prefixLift 3563779
  have htrace : WordTrace (prefixWord ++ tailWord_3563779) baseStart_3563779 baseEnd_3563779 := by
    simpa [prefixWord, tailWord_3563779, baseEnd_3563779] using wordTrace_append hprefix tailTrace_3563779
  have hstable : (prefixWord ++ tailWord_3563779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563779).length < 2 ^ (prefixWord ++ tailWord_3563779).sum := by decide
  have hdescent : baseEnd_3563779 < baseStart_3563779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563809 : List Nat := [1, 2, 3, 2, 1, 1, 4, 3, 2, 2, 2]
def baseStart_3563809 : Nat := 118140960795 + 3563809 * 2 ^ 59
def prefixEnd_3563809 : Nat := 4983230072969 + 3 ^ 40 * 3563809 * 2
def baseEnd_3563809 : Nat := 1829946977819152314597847

theorem tailTrace_3563809 : CollatzResearch.WordTrace tailWord_3563809 prefixEnd_3563809 1829946977819152314597847 := by
  unfold tailWord_3563809
  simp only [CollatzResearch.WordTrace]
  refine ⟨129982792745936117965198481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86655195163957411976798987 129982792745936117965198481)
  ·
    refine ⟨97487094559452088473898861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129982792745936117965198481 97487094559452088473898861)
    ·
      refine ⟨36557660459794533177712073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97487094559452088473898861 36557660459794533177712073)
      ·
        refine ⟨27418245344845899883284055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36557660459794533177712073 27418245344845899883284055)
        ·
          refine ⟨41127368017268849824926083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27418245344845899883284055 41127368017268849824926083)
          ·
            refine ⟨61691052025903274737389125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41127368017268849824926083 61691052025903274737389125)
            ·
              refine ⟨11567072254856864013260461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61691052025903274737389125 11567072254856864013260461)
              ·
                refine ⟨4337652095571324004972673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11567072254856864013260461 4337652095571324004972673)
                ·
                  refine ⟨3253239071678493003729505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4337652095571324004972673 3253239071678493003729505)
                  ·
                    refine ⟨2439929303758869752797129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3253239071678493003729505 2439929303758869752797129)
                    ·
                      refine ⟨1829946977819152314597847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2439929303758869752797129 1829946977819152314597847)
                      ·
                        rfl

theorem cell23_3563809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 3, 2, 2, 2].length) (baseStart_3563809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3563809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3563809 prefixEnd_3563809 := by exact prefixLift 3563809
  have htrace : WordTrace (prefixWord ++ tailWord_3563809) baseStart_3563809 baseEnd_3563809 := by
    simpa [prefixWord, tailWord_3563809, baseEnd_3563809] using wordTrace_append hprefix tailTrace_3563809
  have hstable : (prefixWord ++ tailWord_3563809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563809).length < 2 ^ (prefixWord ++ tailWord_3563809).sum := by decide
  have hdescent : baseEnd_3563809 < baseStart_3563809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563882 : List Nat := [3, 1, 3, 3, 1, 1, 2, 1, 1, 3, 4]
def baseStart_3563882 : Nat := 118140960795 + 3563882 * 2 ^ 59
def prefixEnd_3563882 : Nat := 4983230072969 + 3 ^ 40 * 3563882 * 2
def baseEnd_3563882 : Nat := 1829984461906930528985011

theorem tailTrace_3563882 : CollatzResearch.WordTrace tailWord_3563882 prefixEnd_3563882 1829984461906930528985011 := by
  unfold tailWord_3563882
  simp only [CollatzResearch.WordTrace]
  refine ⟨32496363818667912858151475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86656970183114434288403933 32496363818667912858151475)
  ·
    refine ⟨48744545728001869287227213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32496363818667912858151475 48744545728001869287227213)
    ·
      refine ⟨18279204648000700982710205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48744545728001869287227213 18279204648000700982710205)
      ·
        refine ⟨6854701743000262868516327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18279204648000700982710205 6854701743000262868516327)
        ·
          refine ⟨10282052614500394302774491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6854701743000262868516327 10282052614500394302774491)
          ·
            refine ⟨15423078921750591454161737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10282052614500394302774491 15423078921750591454161737)
            ·
              refine ⟨11567309191312943590621303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15423078921750591454161737 11567309191312943590621303)
              ·
                refine ⟨17350963786969415385931955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11567309191312943590621303 17350963786969415385931955)
                ·
                  refine ⟨26026445680454123078897933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17350963786969415385931955 26026445680454123078897933)
                  ·
                    refine ⟨9759917130170296154586725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26026445680454123078897933 9759917130170296154586725)
                    ·
                      refine ⟨1829984461906930528985011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9759917130170296154586725 1829984461906930528985011)
                      ·
                        rfl

theorem cell23_3563882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_3563882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3563882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3563882 prefixEnd_3563882 := by exact prefixLift 3563882
  have htrace : WordTrace (prefixWord ++ tailWord_3563882) baseStart_3563882 baseEnd_3563882 := by
    simpa [prefixWord, tailWord_3563882, baseEnd_3563882] using wordTrace_append hprefix tailTrace_3563882
  have hstable : (prefixWord ++ tailWord_3563882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563882).length < 2 ^ (prefixWord ++ tailWord_3563882).sum := by decide
  have hdescent : baseEnd_3563882 < baseStart_3563882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563959 : List Nat := [1, 1, 3, 1, 3, 3, 2, 2, 2, 3, 2]
def baseStart_3563959 : Nat := 118140960795 + 3563959 * 2 ^ 59
def prefixEnd_3563959 : Nat := 4983230072969 + 3 ^ 40 * 3563959 * 2
def baseEnd_3563959 : Nat := 1830023999917326727722157

theorem tailTrace_3563959 : CollatzResearch.WordTrace tailWord_3563959 prefixEnd_3563959 1830023999917326727722157 := by
  unfold tailWord_3563959
  simp only [CollatzResearch.WordTrace]
  refine ⟨129988263695392693583158931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86658842463595129055439287 129988263695392693583158931)
  ·
    refine ⟨194982395543089040374738397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129988263695392693583158931 194982395543089040374738397)
    ·
      refine ⟨73118398328658390140526899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194982395543089040374738397 73118398328658390140526899)
      ·
        refine ⟨109677597492987585210790349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73118398328658390140526899 109677597492987585210790349)
        ·
          refine ⟨41129099059870344454046381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109677597492987585210790349 41129099059870344454046381)
          ·
            refine ⟨15423412147451379170267393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41129099059870344454046381 15423412147451379170267393)
            ·
              refine ⟨11567559110588534377700545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15423412147451379170267393 11567559110588534377700545)
              ·
                refine ⟨8675669332941400783275409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11567559110588534377700545 8675669332941400783275409)
                ·
                  refine ⟨6506751999706050587456557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8675669332941400783275409 6506751999706050587456557)
                  ·
                    refine ⟨2440031999889768970296209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6506751999706050587456557 2440031999889768970296209)
                    ·
                      refine ⟨1830023999917326727722157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2440031999889768970296209 1830023999917326727722157)
                      ·
                        rfl

theorem cell23_3563959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2, 2, 3, 2].length) (baseStart_3563959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3563959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3563959 prefixEnd_3563959 := by exact prefixLift 3563959
  have htrace : WordTrace (prefixWord ++ tailWord_3563959) baseStart_3563959 baseEnd_3563959 := by
    simpa [prefixWord, tailWord_3563959, baseEnd_3563959] using wordTrace_append hprefix tailTrace_3563959
  have hstable : (prefixWord ++ tailWord_3563959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563959).length < 2 ^ (prefixWord ++ tailWord_3563959).sum := by decide
  have hdescent : baseEnd_3563959 < baseStart_3563959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563982 : List Nat := [4, 1, 1, 1, 2, 1, 1, 2, 6, 4]
def baseStart_3563982 : Nat := 118140960795 + 3563982 * 2 ^ 59
def prefixEnd_3563982 : Nat := 4983230072969 + 3 ^ 40 * 3563982 * 2
def baseEnd_3563982 : Nat := 610011936657460045911517

theorem tailTrace_3563982 : CollatzResearch.WordTrace tailWord_3563982 prefixEnd_3563982 610011936657460045911517 := by
  unfold tailWord_3563982
  simp only [CollatzResearch.WordTrace]
  refine ⟨16248637821788671063905775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86659401716206245674164133 16248637821788671063905775)
  ·
    refine ⟨24372956732683006595858663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16248637821788671063905775 24372956732683006595858663)
    ·
      refine ⟨36559435099024509893787995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24372956732683006595858663 36559435099024509893787995)
      ·
        refine ⟨54839152648536764840681993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36559435099024509893787995 54839152648536764840681993)
        ·
          refine ⟨41129364486402573630511495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54839152648536764840681993 41129364486402573630511495)
          ·
            refine ⟨61694046729603860445767243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41129364486402573630511495 61694046729603860445767243)
            ·
              refine ⟨92541070094405790668650865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61694046729603860445767243 92541070094405790668650865)
              ·
                refine ⟨69405802570804343001488149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92541070094405790668650865 69405802570804343001488149)
                ·
                  refine ⟨3253396995506453578194757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 69405802570804343001488149 3253396995506453578194757)
                  ·
                    refine ⟨610011936657460045911517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3253396995506453578194757 610011936657460045911517)
                    ·
                      rfl

theorem cell23_3563982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 6, 4].length) (baseStart_3563982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3563982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3563982 prefixEnd_3563982 := by exact prefixLift 3563982
  have htrace : WordTrace (prefixWord ++ tailWord_3563982) baseStart_3563982 baseEnd_3563982 := by
    simpa [prefixWord, tailWord_3563982, baseEnd_3563982] using wordTrace_append hprefix tailTrace_3563982
  have hstable : (prefixWord ++ tailWord_3563982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563982).length < 2 ^ (prefixWord ++ tailWord_3563982).sum := by decide
  have hdescent : baseEnd_3563982 < baseStart_3563982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3563985 : List Nat := [1, 2, 2, 1, 2, 1, 1, 5, 1, 1, 6]
def baseStart_3563985 : Nat := 118140960795 + 3563985 * 2 ^ 59
def prefixEnd_3563985 : Nat := 4983230072969 + 3 ^ 40 * 3563985 * 2
def baseEnd_3563985 : Nat := 1830037350414343625997037

theorem tailTrace_3563985 : CollatzResearch.WordTrace tailWord_3563985 prefixEnd_3563985 1830037350414343625997037 := by
  unfold tailWord_3563985
  simp only [CollatzResearch.WordTrace]
  refine ⟨129989211993298500023605409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86659474662199000015736939 129989211993298500023605409)
  ·
    refine ⟨97491908994973875017704057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129989211993298500023605409 97491908994973875017704057)
    ·
      refine ⟨73118931746230406263278043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97491908994973875017704057 73118931746230406263278043)
      ·
        refine ⟨109678397619345609394917065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73118931746230406263278043 109678397619345609394917065)
        ·
          refine ⟨82258798214509207046187799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109678397619345609394917065 82258798214509207046187799)
          ·
            refine ⟨123388197321763810569281699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82258798214509207046187799 123388197321763810569281699)
            ·
              refine ⟨185082295982645715853922549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123388197321763810569281699 185082295982645715853922549)
              ·
                refine ⟨17351465248373035861305239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 185082295982645715853922549 17351465248373035861305239)
                ·
                  refine ⟨26027197872559553791957859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17351465248373035861305239 26027197872559553791957859)
                  ·
                    refine ⟨39040796808839330687936789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26027197872559553791957859 39040796808839330687936789)
                    ·
                      refine ⟨1830037350414343625997037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39040796808839330687936789 1830037350414343625997037)
                      ·
                        rfl

theorem cell23_3563985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 1, 6].length) (baseStart_3563985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3563985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3563985 prefixEnd_3563985 := by exact prefixLift 3563985
  have htrace : WordTrace (prefixWord ++ tailWord_3563985) baseStart_3563985 baseEnd_3563985 := by
    simpa [prefixWord, tailWord_3563985, baseEnd_3563985] using wordTrace_append hprefix tailTrace_3563985
  have hstable : (prefixWord ++ tailWord_3563985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3563985).length < 2 ^ (prefixWord ++ tailWord_3563985).sum := by decide
  have hdescent : baseEnd_3563985 < baseStart_3563985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3563985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564003 : List Nat := [1, 1, 1, 6, 4, 1, 2, 1, 1, 5]
def baseStart_3564003 : Nat := 118140960795 + 3564003 * 2 ^ 59
def prefixEnd_3564003 : Nat := 4983230072969 + 3 ^ 40 * 3564003 * 2
def baseEnd_3564003 : Nat := 610015531022041518523985

theorem tailTrace_3564003 : CollatzResearch.WordTrace tailWord_3564003 prefixEnd_3564003 610015531022041518523985 := by
  unfold tailWord_3564003
  simp only [CollatzResearch.WordTrace]
  refine ⟨129989868507233289097760663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86659912338155526065173775 129989868507233289097760663)
  ·
    refine ⟨194984802760849933646640995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129989868507233289097760663 194984802760849933646640995)
    ·
      refine ⟨292477204141274900469961493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194984802760849933646640995 292477204141274900469961493)
      ·
        refine ⟨13709868944122260959529445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 292477204141274900469961493 13709868944122260959529445)
        ·
          refine ⟨2570600427022923929911771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13709868944122260959529445 2570600427022923929911771)
          ·
            refine ⟨3855900640534385894867657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2570600427022923929911771 3855900640534385894867657)
            ·
              refine ⟨2891925480400789421150743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3855900640534385894867657 2891925480400789421150743)
              ·
                refine ⟨4337888220601184131726115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2891925480400789421150743 4337888220601184131726115)
                ·
                  refine ⟨6506832330901776197589173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4337888220601184131726115 6506832330901776197589173)
                  ·
                    refine ⟨610015531022041518523985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6506832330901776197589173 610015531022041518523985)
                    ·
                      rfl

theorem cell23_3564003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 1, 1, 5].length) (baseStart_3564003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3564003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3564003 prefixEnd_3564003 := by exact prefixLift 3564003
  have htrace : WordTrace (prefixWord ++ tailWord_3564003) baseStart_3564003 baseEnd_3564003 := by
    simpa [prefixWord, tailWord_3564003, baseEnd_3564003] using wordTrace_append hprefix tailTrace_3564003
  have hstable : (prefixWord ++ tailWord_3564003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564003).length < 2 ^ (prefixWord ++ tailWord_3564003).sum := by decide
  have hdescent : baseEnd_3564003 < baseStart_3564003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564015 : List Nat := [1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 6]
def baseStart_3564015 : Nat := 118140960795 + 3564015 * 2 ^ 59
def prefixEnd_3564015 : Nat := 4983230072969 + 3 ^ 40 * 3564015 * 2
def baseEnd_3564015 : Nat := 1830052754833978508621899

theorem tailTrace_3564015 : CollatzResearch.WordTrace tailWord_3564015 prefixEnd_3564015 1830052754833978508621899 := by
  unfold tailWord_3564015
  simp only [CollatzResearch.WordTrace]
  refine ⟨129990306183189815147197499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86660204122126543431464999 129990306183189815147197499)
  ·
    refine ⟨194985459274784722720796249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129990306183189815147197499 194985459274784722720796249)
    ·
      refine ⟨146239094456088542040597187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194985459274784722720796249 146239094456088542040597187)
      ·
        refine ⟨219358641684132813060895781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146239094456088542040597187 219358641684132813060895781)
        ·
          refine ⟨41129745315774902448917959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 219358641684132813060895781 41129745315774902448917959)
          ·
            refine ⟨61694617973662353673376939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41129745315774902448917959 61694617973662353673376939)
            ·
              refine ⟨92541926960493530510065409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61694617973662353673376939 92541926960493530510065409)
              ·
                refine ⟨69406445220370147882549057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92541926960493530510065409 69406445220370147882549057)
                ·
                  refine ⟨52054833915277610911911793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69406445220370147882549057 52054833915277610911911793)
                  ·
                    refine ⟨39041125436458208183933845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52054833915277610911911793 39041125436458208183933845)
                    ·
                      refine ⟨1830052754833978508621899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39041125436458208183933845 1830052754833978508621899)
                      ·
                        rfl

theorem cell23_3564015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 6].length) (baseStart_3564015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3564015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3564015 prefixEnd_3564015 := by exact prefixLift 3564015
  have htrace : WordTrace (prefixWord ++ tailWord_3564015) baseStart_3564015 baseEnd_3564015 := by
    simpa [prefixWord, tailWord_3564015, baseEnd_3564015] using wordTrace_append hprefix tailTrace_3564015
  have hstable : (prefixWord ++ tailWord_3564015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564015).length < 2 ^ (prefixWord ++ tailWord_3564015).sum := by decide
  have hdescent : baseEnd_3564015 < baseStart_3564015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564025 : List Nat := [1, 2, 1, 3, 1, 2, 2, 1, 1, 9]
def baseStart_3564025 : Nat := 118140960795 + 3564025 * 2 ^ 59
def prefixEnd_3564025 : Nat := 4983230072969 + 3 ^ 40 * 3564025 * 2
def baseEnd_3564025 : Nat := 610019296546841156498951

theorem tailTrace_3564025 : CollatzResearch.WordTrace tailWord_3564025 prefixEnd_3564025 610019296546841156498951 := by
  unfold tailWord_3564025
  simp only [CollatzResearch.WordTrace]
  refine ⟨129990670913153586855061529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86660447275435724570041019 129990670913153586855061529)
  ·
    refine ⟨97493003184865190141296147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129990670913153586855061529 97493003184865190141296147)
    ·
      refine ⟨146239504777297785211944221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97493003184865190141296147 146239504777297785211944221)
      ·
        refine ⟨54839814291486669454479083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146239504777297785211944221 54839814291486669454479083)
        ·
          refine ⟨82259721437230004181718625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54839814291486669454479083 82259721437230004181718625)
          ·
            refine ⟨61694791077922503136288969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82259721437230004181718625 61694791077922503136288969)
            ·
              refine ⟨46271093308441877352216727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61694791077922503136288969 46271093308441877352216727)
              ·
                refine ⟨69406639962662816028325091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46271093308441877352216727 69406639962662816028325091)
                ·
                  refine ⟨104109959943994224042487637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69406639962662816028325091 104109959943994224042487637)
                  ·
                    refine ⟨610019296546841156498951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 104109959943994224042487637 610019296546841156498951)
                    ·
                      rfl

theorem cell23_3564025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 9].length) (baseStart_3564025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3564025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3564025 prefixEnd_3564025 := by exact prefixLift 3564025
  have htrace : WordTrace (prefixWord ++ tailWord_3564025) baseStart_3564025 baseEnd_3564025 := by
    simpa [prefixWord, tailWord_3564025, baseEnd_3564025] using wordTrace_append hprefix tailTrace_3564025
  have hstable : (prefixWord ++ tailWord_3564025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564025).length < 2 ^ (prefixWord ++ tailWord_3564025).sum := by decide
  have hdescent : baseEnd_3564025 < baseStart_3564025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564036 : List Nat := [2, 3, 2, 3, 1, 3, 1, 1, 1, 2, 4]
def baseStart_3564036 : Nat := 118140960795 + 3564036 * 2 ^ 59
def prefixEnd_3564036 : Nat := 4983230072969 + 3 ^ 40 * 3564036 * 2
def baseEnd_3564036 : Nat := 1830063537927722926459303

theorem tailTrace_3564036 : CollatzResearch.WordTrace tailWord_3564036 prefixEnd_3564036 1830063537927722926459303 := by
  unfold tailWord_3564036
  simp only [CollatzResearch.WordTrace]
  refine ⟨64995536058056867866855981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86660714744075823822474641 64995536058056867866855981)
  ·
    refine ⟨24373326021771325450070993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64995536058056867866855981 24373326021771325450070993)
    ·
      refine ⟨18279994516328494087553245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24373326021771325450070993 18279994516328494087553245)
      ·
        refine ⟨6854997943623185282832467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18279994516328494087553245 6854997943623185282832467)
        ·
          refine ⟨10282496915434777924248701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6854997943623185282832467 10282496915434777924248701)
          ·
            refine ⟨3855936343288041721593263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10282496915434777924248701 3855936343288041721593263)
            ·
              refine ⟨5783904514932062582389895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3855936343288041721593263 5783904514932062582389895)
              ·
                refine ⟨8675856772398093873584843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5783904514932062582389895 8675856772398093873584843)
                ·
                  refine ⟨13013785158597140810377265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8675856772398093873584843 13013785158597140810377265)
                  ·
                    refine ⟨9760338868947855607782949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13013785158597140810377265 9760338868947855607782949)
                    ·
                      refine ⟨1830063537927722926459303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9760338868947855607782949 1830063537927722926459303)
                      ·
                        rfl

theorem cell23_3564036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_3564036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3564036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3564036 prefixEnd_3564036 := by exact prefixLift 3564036
  have htrace : WordTrace (prefixWord ++ tailWord_3564036) baseStart_3564036 baseEnd_3564036 := by
    simpa [prefixWord, tailWord_3564036, baseEnd_3564036] using wordTrace_append hprefix tailTrace_3564036
  have hstable : (prefixWord ++ tailWord_3564036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564036).length < 2 ^ (prefixWord ++ tailWord_3564036).sum := by decide
  have hdescent : baseEnd_3564036 < baseStart_3564036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564112 : List Nat := [2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 3]
def baseStart_3564112 : Nat := 118140960795 + 3564112 * 2 ^ 59
def prefixEnd_3564112 : Nat := 4983230072969 + 3 ^ 40 * 3564112 * 2
def baseEnd_3564112 : Nat := 1830102562457464629108953

theorem tailTrace_3564112 : CollatzResearch.WordTrace tailWord_3564112 prefixEnd_3564112 1830102562457464629108953 := by
  unfold tailWord_3564112
  simp only [CollatzResearch.WordTrace]
  refine ⟨64996922031919200356739295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86662562709225600475652393 64996922031919200356739295)
  ·
    refine ⟨97495383047878800535108943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64996922031919200356739295 97495383047878800535108943)
    ·
      refine ⟨146243074571818200802663415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97495383047878800535108943 146243074571818200802663415)
      ·
        refine ⟨219364611857727301203995123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146243074571818200802663415 219364611857727301203995123)
        ·
          refine ⟨329046917786590951805992685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219364611857727301203995123 329046917786590951805992685)
          ·
            refine ⟨123392594169971606927247257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 329046917786590951805992685 123392594169971606927247257)
            ·
              refine ⟨92544445627478705195435443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123392594169971606927247257 92544445627478705195435443)
              ·
                refine ⟨138816668441218057793153165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92544445627478705195435443 138816668441218057793153165)
                ·
                  refine ⟨52056250665456771672432437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138816668441218057793153165 52056250665456771672432437)
                  ·
                    refine ⟨4880273499886572344290541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52056250665456771672432437 4880273499886572344290541)
                    ·
                      refine ⟨1830102562457464629108953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4880273499886572344290541 1830102562457464629108953)
                      ·
                        rfl

theorem cell23_3564112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 3].length) (baseStart_3564112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3564112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3564112 prefixEnd_3564112 := by exact prefixLift 3564112
  have htrace : WordTrace (prefixWord ++ tailWord_3564112) baseStart_3564112 baseEnd_3564112 := by
    simpa [prefixWord, tailWord_3564112, baseEnd_3564112] using wordTrace_append hprefix tailTrace_3564112
  have hstable : (prefixWord ++ tailWord_3564112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564112).length < 2 ^ (prefixWord ++ tailWord_3564112).sum := by decide
  have hdescent : baseEnd_3564112 < baseStart_3564112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564119 : List Nat := [1, 1, 3, 2, 2, 2, 2, 5, 5]
def baseStart_3564119 : Nat := 118140960795 + 3564119 * 2 ^ 59
def prefixEnd_3564119 : Nat := 4983230072969 + 3 ^ 40 * 3564119 * 2
def baseEnd_3564119 : Nat := 203345128535782900191269

theorem tailTrace_3564119 : CollatzResearch.WordTrace tailWord_3564119 prefixEnd_3564119 203345128535782900191269 := by
  unfold tailWord_3564119
  simp only [CollatzResearch.WordTrace]
  refine ⟨129994099374813040908983411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86662732916542027272655607 129994099374813040908983411)
  ·
    refine ⟨194991149062219561363475117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129994099374813040908983411 194991149062219561363475117)
    ·
      refine ⟨73121680898332335511303169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194991149062219561363475117 73121680898332335511303169)
      ·
        refine ⟨54841260673749251633477377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73121680898332335511303169 54841260673749251633477377)
        ·
          refine ⟨41130945505311938725108033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54841260673749251633477377 41130945505311938725108033)
          ·
            refine ⟨30848209128983954043831025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41130945505311938725108033 30848209128983954043831025)
            ·
              refine ⟨23136156846737965532873269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30848209128983954043831025 23136156846737965532873269)
              ·
                refine ⟨2169014704381684268706869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23136156846737965532873269 2169014704381684268706869)
                ·
                  refine ⟨203345128535782900191269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2169014704381684268706869 203345128535782900191269)
                  ·
                    rfl

theorem cell23_3564119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 5, 5].length) (baseStart_3564119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3564119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3564119 prefixEnd_3564119 := by exact prefixLift 3564119
  have htrace : WordTrace (prefixWord ++ tailWord_3564119) baseStart_3564119 baseEnd_3564119 := by
    simpa [prefixWord, tailWord_3564119, baseEnd_3564119] using wordTrace_append hprefix tailTrace_3564119
  have hstable : (prefixWord ++ tailWord_3564119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564119).length < 2 ^ (prefixWord ++ tailWord_3564119).sum := by decide
  have hdescent : baseEnd_3564119 < baseStart_3564119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564146 : List Nat := [3, 2, 1, 2, 4, 1, 1, 1, 2, 3, 3]
def baseStart_3564146 : Nat := 118140960795 + 3564146 * 2 ^ 59
def prefixEnd_3564146 : Nat := 4983230072969 + 3 ^ 40 * 3564146 * 2
def baseEnd_3564146 : Nat := 1830120020799717496083797

theorem tailTrace_3564146 : CollatzResearch.WordTrace tailWord_3564146 prefixEnd_3564146 1830120020799717496083797 := by
  unfold tailWord_3564146
  simp only [CollatzResearch.WordTrace]
  refine ⟨32498771036428806130054073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86663389430476816346810861 32498771036428806130054073)
  ·
    refine ⟨24374078277321604597540555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32498771036428806130054073 24374078277321604597540555)
    ·
      refine ⟨36561117415982406896310833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24374078277321604597540555 36561117415982406896310833)
      ·
        refine ⟨27420838061986805172233125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36561117415982406896310833 27420838061986805172233125)
        ·
          refine ⟨5141407136622525969793711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27420838061986805172233125 5141407136622525969793711)
          ·
            refine ⟨7712110704933788954690567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5141407136622525969793711 7712110704933788954690567)
            ·
              refine ⟨11568166057400683432035851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7712110704933788954690567 11568166057400683432035851)
              ·
                refine ⟨17352249086101025148053777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11568166057400683432035851 17352249086101025148053777)
                ·
                  refine ⟨13014186814575768861040333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17352249086101025148053777 13014186814575768861040333)
                  ·
                    refine ⟨4880320055465913322890125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13014186814575768861040333 4880320055465913322890125)
                    ·
                      refine ⟨1830120020799717496083797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4880320055465913322890125 1830120020799717496083797)
                      ·
                        rfl

theorem cell23_3564146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_3564146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3564146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3564146 prefixEnd_3564146 := by exact prefixLift 3564146
  have htrace : WordTrace (prefixWord ++ tailWord_3564146) baseStart_3564146 baseEnd_3564146 := by
    simpa [prefixWord, tailWord_3564146, baseEnd_3564146] using wordTrace_append hprefix tailTrace_3564146
  have hstable : (prefixWord ++ tailWord_3564146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564146).length < 2 ^ (prefixWord ++ tailWord_3564146).sum := by decide
  have hdescent : baseEnd_3564146 < baseStart_3564146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564152 : List Nat := [2, 1, 2, 1, 1, 1, 2, 3, 3, 3, 4]
def baseStart_3564152 : Nat := 118140960795 + 3564152 * 2 ^ 59
def prefixEnd_3564152 : Nat := 4983230072969 + 3 ^ 40 * 3564152 * 2
def baseEnd_3564152 : Nat := 1830123101683644472608769

theorem tailTrace_3564152 : CollatzResearch.WordTrace tailWord_3564152 prefixEnd_3564152 1830123101683644472608769 := by
  unfold tailWord_3564152
  simp only [CollatzResearch.WordTrace]
  refine ⟨64997651491846743772467355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86663535322462325029956473 64997651491846743772467355)
  ·
    refine ⟨97496477237770115658701033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64997651491846743772467355 97496477237770115658701033)
    ·
      refine ⟨73122357928327586744025775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97496477237770115658701033 73122357928327586744025775)
      ·
        refine ⟨109683536892491380116038663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73122357928327586744025775 109683536892491380116038663)
        ·
          refine ⟨164525305338737070174057995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109683536892491380116038663 164525305338737070174057995)
          ·
            refine ⟨246787958008105605261086993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164525305338737070174057995 246787958008105605261086993)
            ·
              refine ⟨185090968506079203945815245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246787958008105605261086993 185090968506079203945815245)
              ·
                refine ⟨69409113189779701479680717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 185090968506079203945815245 69409113189779701479680717)
                ·
                  refine ⟨26028417446167388054880269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69409113189779701479680717 26028417446167388054880269)
                  ·
                    refine ⟨9760656542312770520580101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26028417446167388054880269 9760656542312770520580101)
                    ·
                      refine ⟨1830123101683644472608769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9760656542312770520580101 1830123101683644472608769)
                      ·
                        rfl

theorem cell23_3564152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 3, 3, 4].length) (baseStart_3564152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3564152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3564152 prefixEnd_3564152 := by exact prefixLift 3564152
  have htrace : WordTrace (prefixWord ++ tailWord_3564152) baseStart_3564152 baseEnd_3564152 := by
    simpa [prefixWord, tailWord_3564152, baseEnd_3564152] using wordTrace_append hprefix tailTrace_3564152
  have hstable : (prefixWord ++ tailWord_3564152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564152).length < 2 ^ (prefixWord ++ tailWord_3564152).sum := by decide
  have hdescent : baseEnd_3564152 < baseStart_3564152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564169 : List Nat := [1, 2, 1, 1, 4, 1, 1, 1, 3, 6, 2]
def baseStart_3564169 : Nat := 118140960795 + 3564169 * 2 ^ 59
def prefixEnd_3564169 : Nat := 4983230072969 + 3 ^ 40 * 3564169 * 2
def baseEnd_3564169 : Nat := 1830131830854770906096191

theorem tailTrace_3564169 : CollatzResearch.WordTrace tailWord_3564169 prefixEnd_3564169 1830131830854770906096191 := by
  unfold tailWord_3564169
  simp only [CollatzResearch.WordTrace]
  refine ⟨129995923024631899448303561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86663948683087932965535707 129995923024631899448303561)
  ·
    refine ⟨97496942268473924586227671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129995923024631899448303561 97496942268473924586227671)
    ·
      refine ⟨146245413402710886879341507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97496942268473924586227671 146245413402710886879341507)
      ·
        refine ⟨219368120104066330319012261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146245413402710886879341507 219368120104066330319012261)
        ·
          refine ⟨41131522519512436934814799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 219368120104066330319012261 41131522519512436934814799)
          ·
            refine ⟨61697283779268655402222199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41131522519512436934814799 61697283779268655402222199)
            ·
              refine ⟨92545925668902983103333299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61697283779268655402222199 92545925668902983103333299)
              ·
                refine ⟨138818888503354474654999949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92545925668902983103333299 138818888503354474654999949)
                ·
                  refine ⟨52057083188757927995624981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138818888503354474654999949 52057083188757927995624981)
                  ·
                    refine ⟨2440175774473027874794921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 52057083188757927995624981 2440175774473027874794921)
                    ·
                      refine ⟨1830131830854770906096191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2440175774473027874794921 1830131830854770906096191)
                      ·
                        rfl

theorem cell23_3564169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 6, 2].length) (baseStart_3564169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3564169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3564169 prefixEnd_3564169 := by exact prefixLift 3564169
  have htrace : WordTrace (prefixWord ++ tailWord_3564169) baseStart_3564169 baseEnd_3564169 := by
    simpa [prefixWord, tailWord_3564169, baseEnd_3564169] using wordTrace_append hprefix tailTrace_3564169
  have hstable : (prefixWord ++ tailWord_3564169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564169).length < 2 ^ (prefixWord ++ tailWord_3564169).sum := by decide
  have hdescent : baseEnd_3564169 < baseStart_3564169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564172 : List Nat := [2, 2, 1, 2, 1, 1, 2, 2, 2, 3, 5]
def baseStart_3564172 : Nat := 118140960795 + 3564172 * 2 ^ 59
def prefixEnd_3564172 : Nat := 4983230072969 + 3 ^ 40 * 3564172 * 2
def baseEnd_3564172 : Nat := 1830133371296734394358677

theorem tailTrace_3564172 : CollatzResearch.WordTrace tailWord_3564172 prefixEnd_3564172 1830133371296734394358677 := by
  unfold tailWord_3564172
  simp only [CollatzResearch.WordTrace]
  refine ⟨64998016221810515480331385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86664021629080687307108513 64998016221810515480331385)
  ·
    refine ⟨48748512166357886610248539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64998016221810515480331385 48748512166357886610248539)
    ·
      refine ⟨73122768249536829915372809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48748512166357886610248539 73122768249536829915372809)
      ·
        refine ⟨54842076187152622436529607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73122768249536829915372809 54842076187152622436529607)
        ·
          refine ⟨82263114280728933654794411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54842076187152622436529607 82263114280728933654794411)
          ·
            refine ⟨123394671421093400482191617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82263114280728933654794411 123394671421093400482191617)
            ·
              refine ⟨92546003565820050361643713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123394671421093400482191617 92546003565820050361643713)
              ·
                refine ⟨69409502674365037771232785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92546003565820050361643713 69409502674365037771232785)
                ·
                  refine ⟨52057127005773778328424589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69409502674365037771232785 52057127005773778328424589)
                  ·
                    refine ⟨19521422627165166873159221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52057127005773778328424589 19521422627165166873159221)
                    ·
                      refine ⟨1830133371296734394358677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19521422627165166873159221 1830133371296734394358677)
                      ·
                        rfl

theorem cell23_3564172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_3564172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3564172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3564172 prefixEnd_3564172 := by exact prefixLift 3564172
  have htrace : WordTrace (prefixWord ++ tailWord_3564172) baseStart_3564172 baseEnd_3564172 := by
    simpa [prefixWord, tailWord_3564172, baseEnd_3564172] using wordTrace_append hprefix tailTrace_3564172
  have hstable : (prefixWord ++ tailWord_3564172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564172).length < 2 ^ (prefixWord ++ tailWord_3564172).sum := by decide
  have hdescent : baseEnd_3564172 < baseStart_3564172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564196 : List Nat := [2, 3, 1, 2, 2, 1, 4, 1, 3, 4]
def baseStart_3564196 : Nat := 118140960795 + 3564196 * 2 ^ 59
def prefixEnd_3564196 : Nat := 4983230072969 + 3 ^ 40 * 3564196 * 2
def baseEnd_3564196 : Nat := 610048564944147433486189

theorem tailTrace_3564196 : CollatzResearch.WordTrace tailWord_3564196 prefixEnd_3564196 610048564944147433486189 := by
  unfold tailWord_3564196
  simp only [CollatzResearch.WordTrace]
  refine ⟨64998453897767041529768221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86664605197022722039690961 64998453897767041529768221)
  ·
    refine ⟨24374420211662640573663083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64998453897767041529768221 24374420211662640573663083)
    ·
      refine ⟨36561630317493960860494625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24374420211662640573663083 36561630317493960860494625)
      ·
        refine ⟨27421222738120470645370969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36561630317493960860494625 27421222738120470645370969)
        ·
          refine ⟨20565917053590352984028227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27421222738120470645370969 20565917053590352984028227)
          ·
            refine ⟨30848875580385529476042341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20565917053590352984028227 30848875580385529476042341)
            ·
              refine ⟨5784164171322286776757939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30848875580385529476042341 5784164171322286776757939)
              ·
                refine ⟨8676246256983430165136909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5784164171322286776757939 8676246256983430165136909)
                ·
                  refine ⟨3253592346368786311926341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8676246256983430165136909 3253592346368786311926341)
                  ·
                    refine ⟨610048564944147433486189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3253592346368786311926341 610048564944147433486189)
                    ·
                      rfl

theorem cell23_3564196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 1, 3, 4].length) (baseStart_3564196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3564196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3564196 prefixEnd_3564196 := by exact prefixLift 3564196
  have htrace : WordTrace (prefixWord ++ tailWord_3564196) baseStart_3564196 baseEnd_3564196 := by
    simpa [prefixWord, tailWord_3564196, baseEnd_3564196] using wordTrace_append hprefix tailTrace_3564196
  have hstable : (prefixWord ++ tailWord_3564196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564196).length < 2 ^ (prefixWord ++ tailWord_3564196).sum := by decide
  have hdescent : baseEnd_3564196 < baseStart_3564196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564286 : List Nat := [4, 2, 2, 1, 2, 1, 1, 1, 3, 6]
def baseStart_3564286 : Nat := 118140960795 + 3564286 * 2 ^ 59
def prefixEnd_3564286 : Nat := 4983230072969 + 3 ^ 40 * 3564286 * 2
def baseEnd_3564286 : Nat := 610063969363782316111051

theorem tailTrace_3564286 : CollatzResearch.WordTrace tailWord_3564286 prefixEnd_3564286 610063969363782316111051 := by
  unfold tailWord_3564286
  simp only [CollatzResearch.WordTrace]
  refine ⟨16250023795651003553789089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86666793576805352286875141 16250023795651003553789089)
  ·
    refine ⟨12187517846738252665341817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16250023795651003553789089 12187517846738252665341817)
    ·
      refine ⟨9140638385053689499006363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12187517846738252665341817 9140638385053689499006363)
      ·
        refine ⟨13710957577580534248509545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9140638385053689499006363 13710957577580534248509545)
        ·
          refine ⟨10283218183185400686382159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13710957577580534248509545 10283218183185400686382159)
          ·
            refine ⟨15424827274778101029573239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10283218183185400686382159 15424827274778101029573239)
            ·
              refine ⟨23137240912167151544359859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15424827274778101029573239 23137240912167151544359859)
              ·
                refine ⟨34705861368250727316539789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23137240912167151544359859 34705861368250727316539789)
                ·
                  refine ⟨13014698013094022743702421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34705861368250727316539789 13014698013094022743702421)
                  ·
                    refine ⟨610063969363782316111051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13014698013094022743702421 610063969363782316111051)
                    ·
                      rfl

theorem cell23_3564286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_3564286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3564286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3564286 prefixEnd_3564286 := by exact prefixLift 3564286
  have htrace : WordTrace (prefixWord ++ tailWord_3564286) baseStart_3564286 baseEnd_3564286 := by
    simpa [prefixWord, tailWord_3564286, baseEnd_3564286] using wordTrace_append hprefix tailTrace_3564286
  have hstable : (prefixWord ++ tailWord_3564286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564286).length < 2 ^ (prefixWord ++ tailWord_3564286).sum := by decide
  have hdescent : baseEnd_3564286 < baseStart_3564286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564290 : List Nat := [3, 4, 1, 1, 1, 3, 3, 1, 1, 5]
def baseStart_3564290 : Nat := 118140960795 + 3564290 * 2 ^ 59
def prefixEnd_3564290 : Nat := 4983230072969 + 3 ^ 40 * 3564290 * 2
def baseEnd_3564290 : Nat := 610064654004654977561045

theorem tailTrace_3564290 : CollatzResearch.WordTrace tailWord_3564290 prefixEnd_3564290 610064654004654977561045 := by
  unfold tailWord_3564290
  simp only [CollatzResearch.WordTrace]
  refine ⟨32500084064298384278364581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86666890838129024742305549 32500084064298384278364581)
  ·
    refine ⟨6093765762055947052193359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32500084064298384278364581 6093765762055947052193359)
    ·
      refine ⟨9140648643083920578290039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6093765762055947052193359 9140648643083920578290039)
      ·
        refine ⟨13710972964625880867435059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9140648643083920578290039 13710972964625880867435059)
        ·
          refine ⟨20566459446938821301152589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13710972964625880867435059 20566459446938821301152589)
          ·
            refine ⟨7712422292602057987932221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20566459446938821301152589 7712422292602057987932221)
            ·
              refine ⟨2892158359725771745474583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7712422292602057987932221 2892158359725771745474583)
              ·
                refine ⟨4338237539588657618211875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2892158359725771745474583 4338237539588657618211875)
                ·
                  refine ⟨6507356309382986427317813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4338237539588657618211875 6507356309382986427317813)
                  ·
                    refine ⟨610064654004654977561045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6507356309382986427317813 610064654004654977561045)
                    ·
                      rfl

theorem cell23_3564290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_3564290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3564290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3564290 prefixEnd_3564290 := by exact prefixLift 3564290
  have htrace : WordTrace (prefixWord ++ tailWord_3564290) baseStart_3564290 baseEnd_3564290 := by
    simpa [prefixWord, tailWord_3564290, baseEnd_3564290] using wordTrace_append hprefix tailTrace_3564290
  have hstable : (prefixWord ++ tailWord_3564290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564290).length < 2 ^ (prefixWord ++ tailWord_3564290).sum := by decide
  have hdescent : baseEnd_3564290 < baseStart_3564290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564296 : List Nat := [2, 1, 3, 2, 2, 2, 3, 1, 1, 1, 5]
def baseStart_3564296 : Nat := 118140960795 + 3564296 * 2 ^ 59
def prefixEnd_3564296 : Nat := 4983230072969 + 3 ^ 40 * 3564296 * 2
def baseEnd_3564296 : Nat := 1830197042897891909208107

theorem tailTrace_3564296 : CollatzResearch.WordTrace tailWord_3564296 prefixEnd_3564296 1830197042897891909208107 := by
  unfold tailWord_3564296
  simp only [CollatzResearch.WordTrace]
  refine ⟨65000277547585900069088371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86667036730114533425451161 65000277547585900069088371)
  ·
    refine ⟨97500416321378850103632557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65000277547585900069088371 97500416321378850103632557)
    ·
      refine ⟨36562656120517068788862209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97500416321378850103632557 36562656120517068788862209)
      ·
        refine ⟨27421992090387801591646657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36562656120517068788862209 27421992090387801591646657)
        ·
          refine ⟨20566494067790851193734993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27421992090387801591646657 20566494067790851193734993)
          ·
            refine ⟨15424870550843138395301245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20566494067790851193734993 15424870550843138395301245)
            ·
              refine ⟨5784326456566176898237967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15424870550843138395301245 5784326456566176898237967)
              ·
                refine ⟨8676489684849265347356951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5784326456566176898237967 8676489684849265347356951)
                ·
                  refine ⟨13014734527273898021035427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8676489684849265347356951 13014734527273898021035427)
                  ·
                    refine ⟨19522101790910847031553141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13014734527273898021035427 19522101790910847031553141)
                    ·
                      refine ⟨1830197042897891909208107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19522101790910847031553141 1830197042897891909208107)
                      ·
                        rfl

theorem cell23_3564296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_3564296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3564296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3564296 prefixEnd_3564296 := by exact prefixLift 3564296
  have htrace : WordTrace (prefixWord ++ tailWord_3564296) baseStart_3564296 baseEnd_3564296 := by
    simpa [prefixWord, tailWord_3564296, baseEnd_3564296] using wordTrace_append hprefix tailTrace_3564296
  have hstable : (prefixWord ++ tailWord_3564296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564296).length < 2 ^ (prefixWord ++ tailWord_3564296).sum := by decide
  have hdescent : baseEnd_3564296 < baseStart_3564296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564316 : List Nat := [2, 2, 3, 1, 1, 5, 1, 8]
def baseStart_3564316 : Nat := 118140960795 + 3564316 * 2 ^ 59
def prefixEnd_3564316 : Nat := 4983230072969 + 3 ^ 40 * 3564316 * 2
def baseEnd_3564316 : Nat := 67785456018925252998445

theorem tailTrace_3564316 : CollatzResearch.WordTrace tailWord_3564316 prefixEnd_3564316 67785456018925252998445 := by
  unfold tailWord_3564316
  simp only [CollatzResearch.WordTrace]
  refine ⟨65000642277549671776952401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86667523036732895702603201 65000642277549671776952401)
  ·
    refine ⟨48750481708162253832714301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65000642277549671776952401 48750481708162253832714301)
    ·
      refine ⟨18281430640560845187267863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48750481708162253832714301 18281430640560845187267863)
      ·
        refine ⟨27422145960841267780901795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18281430640560845187267863 27422145960841267780901795)
        ·
          refine ⟨41133218941261901671352693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27422145960841267780901795 41133218941261901671352693)
          ·
            refine ⟨3856239275743303281689315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41133218941261901671352693 3856239275743303281689315)
            ·
              refine ⟨5784358913614954922533973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3856239275743303281689315 5784358913614954922533973)
              ·
                refine ⟨67785456018925252998445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5784358913614954922533973 67785456018925252998445)
                ·
                  rfl

theorem cell23_3564316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 8].length) (baseStart_3564316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3564316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3564316 prefixEnd_3564316 := by exact prefixLift 3564316
  have htrace : WordTrace (prefixWord ++ tailWord_3564316) baseStart_3564316 baseEnd_3564316 := by
    simpa [prefixWord, tailWord_3564316, baseEnd_3564316] using wordTrace_append hprefix tailTrace_3564316
  have hstable : (prefixWord ++ tailWord_3564316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564316).length < 2 ^ (prefixWord ++ tailWord_3564316).sum := by decide
  have hdescent : baseEnd_3564316 < baseStart_3564316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564379 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 7, 4, 4]
def baseStart_3564379 : Nat := 118140960795 + 3564379 * 2 ^ 59
def prefixEnd_3564379 : Nat := 4983230072969 + 3 ^ 40 * 3564379 * 2
def baseEnd_3564379 : Nat := 1830239661792215084470225

theorem tailTrace_3564379 : CollatzResearch.WordTrace tailWord_3564379 prefixEnd_3564379 1830239661792215084470225 := by
  unfold tailWord_3564379
  simp only [CollatzResearch.WordTrace]
  refine ⟨130003582353871105313448191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86669054902580736875632127 130003582353871105313448191)
  ·
    refine ⟨195005373530806657970172287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130003582353871105313448191 195005373530806657970172287)
    ·
      refine ⟨292508060296209986955258431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195005373530806657970172287 292508060296209986955258431)
      ·
        refine ⟨438762090444314980432887647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292508060296209986955258431 438762090444314980432887647)
        ·
          refine ⟨658143135666472470649331471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 438762090444314980432887647 658143135666472470649331471)
          ·
            refine ⟨987214703499708705973997207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 658143135666472470649331471 987214703499708705973997207)
            ·
              refine ⟨1480822055249563058960995811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 987214703499708705973997207 1480822055249563058960995811)
              ·
                refine ⟨2221233082874344588441493717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1480822055249563058960995811 2221233082874344588441493717)
                ·
                  refine ⟨52060150379867451291597509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2221233082874344588441493717 52060150379867451291597509)
                  ·
                    refine ⟨9761278196225147117174533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52060150379867451291597509 9761278196225147117174533)
                    ·
                      refine ⟨1830239661792215084470225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9761278196225147117174533 1830239661792215084470225)
                      ·
                        rfl

theorem cell23_3564379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 4, 4].length) (baseStart_3564379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3564379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3564379 prefixEnd_3564379 := by exact prefixLift 3564379
  have htrace : WordTrace (prefixWord ++ tailWord_3564379) baseStart_3564379 baseEnd_3564379 := by
    simpa [prefixWord, tailWord_3564379, baseEnd_3564379] using wordTrace_append hprefix tailTrace_3564379
  have hstable : (prefixWord ++ tailWord_3564379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564379).length < 2 ^ (prefixWord ++ tailWord_3564379).sum := by decide
  have hdescent : baseEnd_3564379 < baseStart_3564379 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564416 : List Nat := [2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 3]
def baseStart_3564416 : Nat := 118140960795 + 3564416 * 2 ^ 59
def prefixEnd_3564416 : Nat := 4983230072969 + 3 ^ 40 * 3564416 * 2
def baseEnd_3564416 : Nat := 1830258660576431439707555

theorem tailTrace_3564416 : CollatzResearch.WordTrace tailWord_3564416 prefixEnd_3564416 1830258660576431439707555 := by
  unfold tailWord_3564416
  simp only [CollatzResearch.WordTrace]
  refine ⟨65002465927368530316272551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86669954569824707088363401 65002465927368530316272551)
  ·
    refine ⟨97503698891052795474408827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65002465927368530316272551 97503698891052795474408827)
    ·
      refine ⟨146255548336579193211613241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97503698891052795474408827 146255548336579193211613241)
      ·
        refine ⟨109691661252434394908709931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146255548336579193211613241 109691661252434394908709931)
        ·
          refine ⟨164537491878651592363064897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109691661252434394908709931 164537491878651592363064897)
          ·
            refine ⟨123403118908988694272298673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164537491878651592363064897 123403118908988694272298673)
            ·
              refine ⟨92552339181741520704224005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123403118908988694272298673 92552339181741520704224005)
              ·
                refine ⟨17353563596576535132042001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92552339181741520704224005 17353563596576535132042001)
                ·
                  refine ⟨13015172697432401349031501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17353563596576535132042001 13015172697432401349031501)
                  ·
                    refine ⟨4880689761537150505886813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13015172697432401349031501 4880689761537150505886813)
                    ·
                      refine ⟨1830258660576431439707555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4880689761537150505886813 1830258660576431439707555)
                      ·
                        rfl

theorem cell23_3564416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 3].length) (baseStart_3564416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3564416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3564416 prefixEnd_3564416 := by exact prefixLift 3564416
  have htrace : WordTrace (prefixWord ++ tailWord_3564416) baseStart_3564416 baseEnd_3564416 := by
    simpa [prefixWord, tailWord_3564416, baseEnd_3564416] using wordTrace_append hprefix tailTrace_3564416
  have hstable : (prefixWord ++ tailWord_3564416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564416).length < 2 ^ (prefixWord ++ tailWord_3564416).sum := by decide
  have hdescent : baseEnd_3564416 < baseStart_3564416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564423 : List Nat := [1, 1, 4, 2, 3, 3, 1, 1, 7]
def baseStart_3564423 : Nat := 118140960795 + 3564423 * 2 ^ 59
def prefixEnd_3564423 : Nat := 4983230072969 + 3 ^ 40 * 3564423 * 2
def baseEnd_3564423 : Nat := 203362472771223656924447

theorem tailTrace_3564423 : CollatzResearch.WordTrace tailWord_3564423 prefixEnd_3564423 203362472771223656924447 := by
  unfold tailWord_3564423
  simp only [CollatzResearch.WordTrace]
  refine ⟨130005187165711700828049923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86670124777141133885366615 130005187165711700828049923)
  ·
    refine ⟨195007780748567551242074885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130005187165711700828049923 195007780748567551242074885)
    ·
      refine ⟨36563958890356415857889041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195007780748567551242074885 36563958890356415857889041)
      ·
        refine ⟨27422969167767311893416781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36563958890356415857889041 27422969167767311893416781)
        ·
          refine ⟨10283613437912741960031293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27422969167767311893416781 10283613437912741960031293)
          ·
            refine ⟨3856355039217278235011735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10283613437912741960031293 3856355039217278235011735)
            ·
              refine ⟨5784532558825917352517603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3856355039217278235011735 5784532558825917352517603)
              ·
                refine ⟨8676798838238876028776405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5784532558825917352517603 8676798838238876028776405)
                ·
                  refine ⟨203362472771223656924447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8676798838238876028776405 203362472771223656924447)
                  ·
                    rfl

theorem cell23_3564423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 1, 7].length) (baseStart_3564423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3564423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3564423 prefixEnd_3564423 := by exact prefixLift 3564423
  have htrace : WordTrace (prefixWord ++ tailWord_3564423) baseStart_3564423 baseEnd_3564423 := by
    simpa [prefixWord, tailWord_3564423, baseEnd_3564423] using wordTrace_append hprefix tailTrace_3564423
  have hstable : (prefixWord ++ tailWord_3564423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564423).length < 2 ^ (prefixWord ++ tailWord_3564423).sum := by decide
  have hdescent : baseEnd_3564423 < baseStart_3564423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564434 : List Nat := [3, 2, 3, 2, 2, 1, 1, 3, 2, 2, 2]
def baseStart_3564434 : Nat := 118140960795 + 3564434 * 2 ^ 59
def prefixEnd_3564434 : Nat := 4983230072969 + 3 ^ 40 * 3564434 * 2
def baseEnd_3564434 : Nat := 1830267903228212369282473

theorem tailTrace_3564434 : CollatzResearch.WordTrace tailWord_3564434 prefixEnd_3564434 1830267903228212369282473 := by
  unfold tailWord_3564434
  simp only [CollatzResearch.WordTrace]
  refine ⟨32501397092167962426675089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86670392245781233137800237 32501397092167962426675089)
  ·
    refine ⟨24376047819125971820006317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32501397092167962426675089 24376047819125971820006317)
    ·
      refine ⟨9141017932172239432502369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24376047819125971820006317 9141017932172239432502369)
      ·
        refine ⟨6855763449129179574376777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9141017932172239432502369 6855763449129179574376777)
        ·
          refine ⟨5141822586846884680782583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6855763449129179574376777 5141822586846884680782583)
          ·
            refine ⟨7712733880270327021173875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5141822586846884680782583 7712733880270327021173875)
            ·
              refine ⟨11569100820405490531760813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7712733880270327021173875 11569100820405490531760813)
              ·
                refine ⟨4338412807652058949410305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11569100820405490531760813 4338412807652058949410305)
                ·
                  refine ⟨3253809605739044212057729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4338412807652058949410305 3253809605739044212057729)
                  ·
                    refine ⟨2440357204304283159043297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3253809605739044212057729 2440357204304283159043297)
                    ·
                      refine ⟨1830267903228212369282473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2440357204304283159043297 1830267903228212369282473)
                      ·
                        rfl

theorem cell23_3564434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_3564434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3564434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3564434 prefixEnd_3564434 := by exact prefixLift 3564434
  have htrace : WordTrace (prefixWord ++ tailWord_3564434) baseStart_3564434 baseEnd_3564434 := by
    simpa [prefixWord, tailWord_3564434, baseEnd_3564434] using wordTrace_append hprefix tailTrace_3564434
  have hstable : (prefixWord ++ tailWord_3564434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564434).length < 2 ^ (prefixWord ++ tailWord_3564434).sum := by decide
  have hdescent : baseEnd_3564434 < baseStart_3564434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564473 : List Nat := [1, 2, 1, 4, 2, 2, 2, 2, 2, 1, 4]
def baseStart_3564473 : Nat := 118140960795 + 3564473 * 2 ^ 59
def prefixEnd_3564473 : Nat := 4983230072969 + 3 ^ 40 * 3564473 * 2
def baseEnd_3564473 : Nat := 1830287928973737716694793

theorem tailTrace_3564473 : CollatzResearch.WordTrace tailWord_3564473 prefixEnd_3564473 1830287928973737716694793 := by
  unfold tailWord_3564473
  simp only [CollatzResearch.WordTrace]
  refine ⟨130007010815530559367370073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86671340543687039578246715 130007010815530559367370073)
  ·
    refine ⟨97505258111647919525527555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130007010815530559367370073 97505258111647919525527555)
    ·
      refine ⟨146257887167471879288291333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97505258111647919525527555 146257887167471879288291333)
      ·
        refine ⟨27423353843900977366554625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146257887167471879288291333 27423353843900977366554625)
        ·
          refine ⟨20567515382925733024915969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27423353843900977366554625 20567515382925733024915969)
          ·
            refine ⟨15425636537194299768686977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20567515382925733024915969 15425636537194299768686977)
            ·
              refine ⟨11569227402895724826515233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15425636537194299768686977 11569227402895724826515233)
              ·
                refine ⟨8676920552171793619886425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11569227402895724826515233 8676920552171793619886425)
                ·
                  refine ⟨6507690414128845214914819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8676920552171793619886425 6507690414128845214914819)
                  ·
                    refine ⟨9761535621193267822372229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6507690414128845214914819 9761535621193267822372229)
                    ·
                      refine ⟨1830287928973737716694793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9761535621193267822372229 1830287928973737716694793)
                      ·
                        rfl

theorem cell23_3564473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_3564473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3564473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3564473 prefixEnd_3564473 := by exact prefixLift 3564473
  have htrace : WordTrace (prefixWord ++ tailWord_3564473) baseStart_3564473 baseEnd_3564473 := by
    simpa [prefixWord, tailWord_3564473, baseEnd_3564473] using wordTrace_append hprefix tailTrace_3564473
  have hstable : (prefixWord ++ tailWord_3564473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564473).length < 2 ^ (prefixWord ++ tailWord_3564473).sum := by decide
  have hdescent : baseEnd_3564473 < baseStart_3564473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564500 : List Nat := [2, 4, 1, 2, 1, 3, 1, 2, 3, 4]
def baseStart_3564500 : Nat := 118140960795 + 3564500 * 2 ^ 59
def prefixEnd_3564500 : Nat := 4983230072969 + 3 ^ 40 * 3564500 * 2
def baseEnd_3564500 : Nat := 610100597650469703685723

theorem tailTrace_3564500 : CollatzResearch.WordTrace tailWord_3564500 prefixEnd_3564500 610100597650469703685723 := by
  unfold tailWord_3564500
  simp only [CollatzResearch.WordTrace]
  refine ⟨65003997793216371489301477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86671997057621828652401969 65003997793216371489301477)
  ·
    refine ⟨12188249586228069654244027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65003997793216371489301477 12188249586228069654244027)
    ·
      refine ⟨18282374379342104481366041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12188249586228069654244027 18282374379342104481366041)
      ·
        refine ⟨13711780784506578361024531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18282374379342104481366041 13711780784506578361024531)
        ·
          refine ⟨20567671176759867541536797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13711780784506578361024531 20567671176759867541536797)
          ·
            refine ⟨7712876691284950328076299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20567671176759867541536797 7712876691284950328076299)
            ·
              refine ⟨11569315036927425492114449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7712876691284950328076299 11569315036927425492114449)
              ·
                refine ⟨8676986277695569119085837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11569315036927425492114449 8676986277695569119085837)
                ·
                  refine ⟨3253869854135838419657189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8676986277695569119085837 3253869854135838419657189)
                  ·
                    refine ⟨610100597650469703685723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3253869854135838419657189 610100597650469703685723)
                    ·
                      rfl

theorem cell23_3564500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_3564500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3564500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3564500 prefixEnd_3564500 := by exact prefixLift 3564500
  have htrace : WordTrace (prefixWord ++ tailWord_3564500) baseStart_3564500 baseEnd_3564500 := by
    simpa [prefixWord, tailWord_3564500, baseEnd_3564500] using wordTrace_append hprefix tailTrace_3564500
  have hstable : (prefixWord ++ tailWord_3564500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564500).length < 2 ^ (prefixWord ++ tailWord_3564500).sum := by decide
  have hdescent : baseEnd_3564500 < baseStart_3564500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564530 : List Nat := [3, 2, 1, 5, 1, 1, 1, 1, 8]
def baseStart_3564530 : Nat := 118140960795 + 3564530 * 2 ^ 59
def prefixEnd_3564530 : Nat := 4983230072969 + 3 ^ 40 * 3564530 * 2
def baseEnd_3564530 : Nat := 203368577485671554853559

theorem tailTrace_3564530 : CollatzResearch.WordTrace tailWord_3564530 prefixEnd_3564530 203368577485671554853559 := by
  unfold tailWord_3564530
  simp only [CollatzResearch.WordTrace]
  refine ⟨32502272444081014525548761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86672726517549372068130029 32502272444081014525548761)
  ·
    refine ⟨24376704333060760894161571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32502272444081014525548761 24376704333060760894161571)
    ·
      refine ⟨36565056499591141341242357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24376704333060760894161571 36565056499591141341242357)
      ·
        refine ⟨3427974046836669500741471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36565056499591141341242357 3427974046836669500741471)
        ·
          refine ⟨5141961070255004251112207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3427974046836669500741471 5141961070255004251112207)
          ·
            refine ⟨7712941605382506376668311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5141961070255004251112207 7712941605382506376668311)
            ·
              refine ⟨11569412408073759565002467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7712941605382506376668311 11569412408073759565002467)
              ·
                refine ⟨17354118612110639347503701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11569412408073759565002467 17354118612110639347503701)
                ·
                  refine ⟨203368577485671554853559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17354118612110639347503701 203368577485671554853559)
                  ·
                    rfl

theorem cell23_3564530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 8].length) (baseStart_3564530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3564530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3564530 prefixEnd_3564530 := by exact prefixLift 3564530
  have htrace : WordTrace (prefixWord ++ tailWord_3564530) baseStart_3564530 baseEnd_3564530 := by
    simpa [prefixWord, tailWord_3564530, baseEnd_3564530] using wordTrace_append hprefix tailTrace_3564530
  have hstable : (prefixWord ++ tailWord_3564530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564530).length < 2 ^ (prefixWord ++ tailWord_3564530).sum := by decide
  have hdescent : baseEnd_3564530 < baseStart_3564530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564540 : List Nat := [2, 2, 2, 1, 2, 3, 1, 3, 3, 1, 3]
def baseStart_3564540 : Nat := 118140960795 + 3564540 * 2 ^ 59
def prefixEnd_3564540 : Nat := 4983230072969 + 3 ^ 40 * 3564540 * 2
def baseEnd_3564540 : Nat := 1830322332177588954556985

theorem tailTrace_3564540 : CollatzResearch.WordTrace tailWord_3564540 prefixEnd_3564540 1830322332177588954556985 := by
  unfold tailWord_3564540
  simp only [CollatzResearch.WordTrace]
  refine ⟨65004727253143914905029537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86672969670858553206706049 65004727253143914905029537)
  ·
    refine ⟨48753545439857936178772153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65004727253143914905029537 48753545439857936178772153)
    ·
      refine ⟨36565159079893452134079115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48753545439857936178772153 36565159079893452134079115)
      ·
        refine ⟨54847738619840178201118673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36565159079893452134079115 54847738619840178201118673)
        ·
          refine ⟨41135803964880133650839005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54847738619840178201118673 41135803964880133650839005)
          ·
            refine ⟨15425926486830050119064627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41135803964880133650839005 15425926486830050119064627)
            ·
              refine ⟨23138889730245075178596941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15425926486830050119064627 23138889730245075178596941)
              ·
                refine ⟨8677083648841903191973853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23138889730245075178596941 8677083648841903191973853)
                ·
                  refine ⟨3253906368315713696990195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8677083648841903191973853 3253906368315713696990195)
                  ·
                    refine ⟨4880859552473570545485293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3253906368315713696990195 4880859552473570545485293)
                    ·
                      refine ⟨1830322332177588954556985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4880859552473570545485293 1830322332177588954556985)
                      ·
                        rfl

theorem cell23_3564540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3, 3, 1, 3].length) (baseStart_3564540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3564540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3564540 prefixEnd_3564540 := by exact prefixLift 3564540
  have htrace : WordTrace (prefixWord ++ tailWord_3564540) baseStart_3564540 baseEnd_3564540 := by
    simpa [prefixWord, tailWord_3564540, baseEnd_3564540] using wordTrace_append hprefix tailTrace_3564540
  have hstable : (prefixWord ++ tailWord_3564540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564540).length < 2 ^ (prefixWord ++ tailWord_3564540).sum := by decide
  have hdescent : baseEnd_3564540 < baseStart_3564540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564563 : List Nat := [1, 1, 1, 2, 1, 4, 1, 1, 1, 8, 2]
def baseStart_3564563 : Nat := 118140960795 + 3564563 * 2 ^ 59
def prefixEnd_3564563 : Nat := 4983230072969 + 3 ^ 40 * 3564563 * 2
def baseEnd_3564563 : Nat := 1830334142232642364569379

theorem tailTrace_3564563 : CollatzResearch.WordTrace tailWord_3564563 prefixEnd_3564563 1830334142232642364569379 := by
  unfold tailWord_3564563
  simp only [CollatzResearch.WordTrace]
  refine ⟨130010293385204504738146343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86673528923469669825430895 130010293385204504738146343)
  ·
    refine ⟨195015440077806757107219515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130010293385204504738146343 195015440077806757107219515)
    ·
      refine ⟨292523160116710135660829273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195015440077806757107219515 292523160116710135660829273)
      ·
        refine ⟨219392370087532601745621955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292523160116710135660829273 219392370087532601745621955)
        ·
          refine ⟨329088555131298902618432933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219392370087532601745621955 329088555131298902618432933)
          ·
            refine ⟨61704104087118544240956175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 329088555131298902618432933 61704104087118544240956175)
            ·
              refine ⟨92556156130677816361434263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61704104087118544240956175 92556156130677816361434263)
              ·
                refine ⟨138834234196016724542151395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92556156130677816361434263 138834234196016724542151395)
                ·
                  refine ⟨208251351294025086813227093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138834234196016724542151395 208251351294025086813227093)
                  ·
                    refine ⟨2440445522976856486092505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 208251351294025086813227093 2440445522976856486092505)
                    ·
                      refine ⟨1830334142232642364569379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2440445522976856486092505 1830334142232642364569379)
                      ·
                        rfl

theorem cell23_3564563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 8, 2].length) (baseStart_3564563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3564563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3564563 prefixEnd_3564563 := by exact prefixLift 3564563
  have htrace : WordTrace (prefixWord ++ tailWord_3564563) baseStart_3564563 baseEnd_3564563 := by
    simpa [prefixWord, tailWord_3564563, baseEnd_3564563] using wordTrace_append hprefix tailTrace_3564563
  have hstable : (prefixWord ++ tailWord_3564563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564563).length < 2 ^ (prefixWord ++ tailWord_3564563).sum := by decide
  have hdescent : baseEnd_3564563 < baseStart_3564563 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564590 : List Nat := [4, 1, 3, 1, 1, 1, 1, 3, 4, 4]
def baseStart_3564590 : Nat := 118140960795 + 3564590 * 2 ^ 59
def prefixEnd_3564590 : Nat := 4983230072969 + 3 ^ 40 * 3564590 * 2
def baseEnd_3564590 : Nat := 610116002070104586310585

theorem tailTrace_3564590 : CollatzResearch.WordTrace tailWord_3564590 prefixEnd_3564590 610116002070104586310585 := by
  unfold tailWord_3564590
  simp only [CollatzResearch.WordTrace]
  refine ⟨16251409769513336043672403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86674185437404458899586149 16251409769513336043672403)
  ·
    refine ⟨24377114654270004065508605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16251409769513336043672403 24377114654270004065508605)
    ·
      refine ⟨9141417995351251524565727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24377114654270004065508605 9141417995351251524565727)
      ·
        refine ⟨13712126993026877286848591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9141417995351251524565727 13712126993026877286848591)
        ·
          refine ⟨20568190489540315930272887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13712126993026877286848591 20568190489540315930272887)
          ·
            refine ⟨30852285734310473895409331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20568190489540315930272887 30852285734310473895409331)
            ·
              refine ⟨46278428601465710843113997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30852285734310473895409331 46278428601465710843113997)
              ·
                refine ⟨17354410725549641566167749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46278428601465710843113997 17354410725549641566167749)
                ·
                  refine ⟨3253952011040557793656453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17354410725549641566167749 3253952011040557793656453)
                  ·
                    refine ⟨610116002070104586310585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3253952011040557793656453 610116002070104586310585)
                    ·
                      rfl

theorem cell23_3564590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_3564590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3564590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3564590 prefixEnd_3564590 := by exact prefixLift 3564590
  have htrace : WordTrace (prefixWord ++ tailWord_3564590) baseStart_3564590 baseEnd_3564590 := by
    simpa [prefixWord, tailWord_3564590, baseEnd_3564590] using wordTrace_append hprefix tailTrace_3564590
  have hstable : (prefixWord ++ tailWord_3564590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564590).length < 2 ^ (prefixWord ++ tailWord_3564590).sum := by decide
  have hdescent : baseEnd_3564590 < baseStart_3564590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564614 : List Nat := [6, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4]
def baseStart_3564614 : Nat := 118140960795 + 3564614 * 2 ^ 59
def prefixEnd_3564614 : Nat := 4983230072969 + 3 ^ 40 * 3564614 * 2
def baseEnd_3564614 : Nat := 1830360329746021665031645

theorem tailTrace_3564614 : CollatzResearch.WordTrace tailWord_3564614 prefixEnd_3564614 1830360329746021665031645 := by
  unfold tailWord_3564614
  simp only [CollatzResearch.WordTrace]
  refine ⟨4062879797125616889007903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 86674769005346493632168597 4062879797125616889007903)
  ·
    refine ⟨6094319695688425333511855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4062879797125616889007903 6094319695688425333511855)
    ·
      refine ⟨9141479543532638000267783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6094319695688425333511855 9141479543532638000267783)
      ·
        refine ⟨13712219315298957000401675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9141479543532638000267783 13712219315298957000401675)
        ·
          refine ⟨20568328972948435500602513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13712219315298957000401675 20568328972948435500602513)
          ·
            refine ⟨15426246729711326625451885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20568328972948435500602513 15426246729711326625451885)
            ·
              refine ⟨5784842523641747484544457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15426246729711326625451885 5784842523641747484544457)
              ·
                refine ⟨4338631892731310613408343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5784842523641747484544457 4338631892731310613408343)
                ·
                  refine ⟨6507947839096965920112515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4338631892731310613408343 6507947839096965920112515)
                  ·
                    refine ⟨9761921758645448880168773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6507947839096965920112515 9761921758645448880168773)
                    ·
                      refine ⟨1830360329746021665031645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9761921758645448880168773 1830360329746021665031645)
                      ·
                        rfl

theorem cell23_3564614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_3564614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3564614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3564614 prefixEnd_3564614 := by exact prefixLift 3564614
  have htrace : WordTrace (prefixWord ++ tailWord_3564614) baseStart_3564614 baseEnd_3564614 := by
    simpa [prefixWord, tailWord_3564614, baseEnd_3564614] using wordTrace_append hprefix tailTrace_3564614
  have hstable : (prefixWord ++ tailWord_3564614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564614).length < 2 ^ (prefixWord ++ tailWord_3564614).sum := by decide
  have hdescent : baseEnd_3564614 < baseStart_3564614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564647 : List Nat := [1, 1, 5, 1, 1, 3, 1, 4, 2, 1, 3]
def baseStart_3564647 : Nat := 118140960795 + 3564647 * 2 ^ 59
def prefixEnd_3564647 : Nat := 4983230072969 + 3 ^ 40 * 3564647 * 2
def baseEnd_3564647 : Nat := 1830377274607620035918993

theorem tailTrace_3564647 : CollatzResearch.WordTrace tailWord_3564647 prefixEnd_3564647 1830377274607620035918993 := by
  unfold tailWord_3564647
  simp only [CollatzResearch.WordTrace]
  refine ⟨130013357116900187084204195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86675571411266791389469463 130013357116900187084204195)
  ·
    refine ⟨195020035675350280626306293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130013357116900187084204195 195020035675350280626306293)
    ·
      refine ⟨18283128344564088808716215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 195020035675350280626306293 18283128344564088808716215)
      ·
        refine ⟨27424692516846133213074323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18283128344564088808716215 27424692516846133213074323)
        ·
          refine ⟨41137038775269199819611485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27424692516846133213074323 41137038775269199819611485)
          ·
            refine ⟨15426389540725949932354307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41137038775269199819611485 15426389540725949932354307)
            ·
              refine ⟨23139584311088924898531461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15426389540725949932354307 23139584311088924898531461)
              ·
                refine ⟨4338672058329173418474649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23139584311088924898531461 4338672058329173418474649)
                ·
                  refine ⟨3254004043746880063855987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4338672058329173418474649 3254004043746880063855987)
                  ·
                    refine ⟨4881006065620320095783981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3254004043746880063855987 4881006065620320095783981)
                    ·
                      refine ⟨1830377274607620035918993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4881006065620320095783981 1830377274607620035918993)
                      ·
                        rfl

theorem cell23_3564647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 4, 2, 1, 3].length) (baseStart_3564647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3564647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3564647 prefixEnd_3564647 := by exact prefixLift 3564647
  have htrace : WordTrace (prefixWord ++ tailWord_3564647) baseStart_3564647 baseEnd_3564647 := by
    simpa [prefixWord, tailWord_3564647, baseEnd_3564647] using wordTrace_append hprefix tailTrace_3564647
  have hstable : (prefixWord ++ tailWord_3564647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564647).length < 2 ^ (prefixWord ++ tailWord_3564647).sum := by decide
  have hdescent : baseEnd_3564647 < baseStart_3564647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564648 : List Nat := [2, 1, 4, 4, 1, 1, 1, 4, 1, 2, 2]
def baseStart_3564648 : Nat := 118140960795 + 3564648 * 2 ^ 59
def prefixEnd_3564648 : Nat := 4983230072969 + 3 ^ 40 * 3564648 * 2
def baseEnd_3564648 : Nat := 1830377788088274532006489

theorem tailTrace_3564648 : CollatzResearch.WordTrace tailWord_3564648 prefixEnd_3564648 1830377788088274532006489 := by
  unfold tailWord_3564648
  simp only [CollatzResearch.WordTrace]
  refine ⟨65006696794948282127495299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86675595726597709503327065 65006696794948282127495299)
  ·
    refine ⟨97510045192422423191242949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65006696794948282127495299 97510045192422423191242949)
    ·
      refine ⟨18283133473579204348358053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97510045192422423191242949 18283133473579204348358053)
      ·
        refine ⟨3428087526296100815317135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18283133473579204348358053 3428087526296100815317135)
        ·
          refine ⟨5142131289444151222975703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3428087526296100815317135 5142131289444151222975703)
          ·
            refine ⟨7713196934166226834463555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5142131289444151222975703 7713196934166226834463555)
            ·
              refine ⟨11569795401249340251695333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7713196934166226834463555 11569795401249340251695333)
              ·
                refine ⟨2169336637734251297192875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11569795401249340251695333 2169336637734251297192875)
                ·
                  refine ⟨3254004956601376945789313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2169336637734251297192875 3254004956601376945789313)
                  ·
                    refine ⟨2440503717451032709341985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3254004956601376945789313 2440503717451032709341985)
                    ·
                      refine ⟨1830377788088274532006489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2440503717451032709341985 1830377788088274532006489)
                      ·
                        rfl

theorem cell23_3564648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_3564648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3564648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3564648 prefixEnd_3564648 := by exact prefixLift 3564648
  have htrace : WordTrace (prefixWord ++ tailWord_3564648) baseStart_3564648 baseEnd_3564648 := by
    simpa [prefixWord, tailWord_3564648, baseEnd_3564648] using wordTrace_append hprefix tailTrace_3564648
  have hstable : (prefixWord ++ tailWord_3564648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564648).length < 2 ^ (prefixWord ++ tailWord_3564648).sum := by decide
  have hdescent : baseEnd_3564648 < baseStart_3564648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564663 : List Nat := [1, 1, 3, 1, 1, 4, 3, 1, 2, 6]
def baseStart_3564663 : Nat := 118140960795 + 3564663 * 2 ^ 59
def prefixEnd_3564663 : Nat := 4983230072969 + 3 ^ 40 * 3564663 * 2
def baseEnd_3564663 : Nat := 610128496766030657772973

theorem tailTrace_3564663 : CollatzResearch.WordTrace tailWord_3564663 prefixEnd_3564663 610128496766030657772973 := by
  unfold tailWord_3564663
  simp only [CollatzResearch.WordTrace]
  refine ⟨130013940684842221816786643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86675960456561481211191095 130013940684842221816786643)
  ·
    refine ⟨195020911027263332725179965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130013940684842221816786643 195020911027263332725179965)
    ·
      refine ⟨73132841635223749771942487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195020911027263332725179965 73132841635223749771942487)
      ·
        refine ⟨109699262452835624657913731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73132841635223749771942487 109699262452835624657913731)
        ·
          refine ⟨164548893679253436986870597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109699262452835624657913731 164548893679253436986870597)
          ·
            refine ⟨30852917564860019435038237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 164548893679253436986870597 30852917564860019435038237)
            ·
              refine ⟨11569844086822507288139339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30852917564860019435038237 11569844086822507288139339)
              ·
                refine ⟨17354766130233760932209009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11569844086822507288139339 17354766130233760932209009)
                ·
                  refine ⟨13016074597675320699156757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17354766130233760932209009 13016074597675320699156757)
                  ·
                    refine ⟨610128496766030657772973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13016074597675320699156757 610128496766030657772973)
                    ·
                      rfl

theorem cell23_3564663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 2, 6].length) (baseStart_3564663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3564663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3564663 prefixEnd_3564663 := by exact prefixLift 3564663
  have htrace : WordTrace (prefixWord ++ tailWord_3564663) baseStart_3564663 baseEnd_3564663 := by
    simpa [prefixWord, tailWord_3564663, baseEnd_3564663] using wordTrace_append hprefix tailTrace_3564663
  have hstable : (prefixWord ++ tailWord_3564663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564663).length < 2 ^ (prefixWord ++ tailWord_3564663).sum := by decide
  have hdescent : baseEnd_3564663 < baseStart_3564663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564700 : List Nat := [2, 2, 3, 2, 1, 2, 1, 2, 2, 2, 4]
def baseStart_3564700 : Nat := 118140960795 + 3564700 * 2 ^ 59
def prefixEnd_3564700 : Nat := 4983230072969 + 3 ^ 40 * 3564700 * 2
def baseEnd_3564700 : Nat := 1830404489082308328556249

theorem tailTrace_3564700 : CollatzResearch.WordTrace tailWord_3564700 prefixEnd_3564700 1830404489082308328556249 := by
  unfold tailWord_3564700
  simp only [CollatzResearch.WordTrace]
  refine ⟨65007645092854088567941777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86676860123805451423922369 65007645092854088567941777)
  ·
    refine ⟨48755733819640566425956333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65007645092854088567941777 48755733819640566425956333)
    ·
      refine ⟨18283400182365212409733625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48755733819640566425956333 18283400182365212409733625)
      ·
        refine ⟨13712550136773909307300219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18283400182365212409733625 13712550136773909307300219)
        ·
          refine ⟨20568825205160863960950329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13712550136773909307300219 20568825205160863960950329)
          ·
            refine ⟨15426618903870647970712747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20568825205160863960950329 15426618903870647970712747)
            ·
              refine ⟨23139928355805971956069121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15426618903870647970712747 23139928355805971956069121)
              ·
                refine ⟨17354946266854478967051841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23139928355805971956069121 17354946266854478967051841)
                ·
                  refine ⟨13016209700140859225288881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17354946266854478967051841 13016209700140859225288881)
                  ·
                    refine ⟨9762157275105644418966661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13016209700140859225288881 9762157275105644418966661)
                    ·
                      refine ⟨1830404489082308328556249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9762157275105644418966661 1830404489082308328556249)
                      ·
                        rfl

theorem cell23_3564700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_3564700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3564700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3564700 prefixEnd_3564700 := by exact prefixLift 3564700
  have htrace : WordTrace (prefixWord ++ tailWord_3564700) baseStart_3564700 baseEnd_3564700 := by
    simpa [prefixWord, tailWord_3564700, baseEnd_3564700] using wordTrace_append hprefix tailTrace_3564700
  have hstable : (prefixWord ++ tailWord_3564700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564700).length < 2 ^ (prefixWord ++ tailWord_3564700).sum := by decide
  have hdescent : baseEnd_3564700 < baseStart_3564700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564723 : List Nat := [1, 1, 1, 2, 3, 2, 3, 2, 1, 7]
def baseStart_3564723 : Nat := 118140960795 + 3564723 * 2 ^ 59
def prefixEnd_3564723 : Nat := 4983230072969 + 3 ^ 40 * 3564723 * 2
def baseEnd_3564723 : Nat := 610138766379120579522881

theorem tailTrace_3564723 : CollatzResearch.WordTrace tailWord_3564723 prefixEnd_3564723 610138766379120579522881 := by
  unfold tailWord_3564723
  simp only [CollatzResearch.WordTrace]
  refine ⟨130016129064624852063970823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86677419376416568042647215 130016129064624852063970823)
  ·
    refine ⟨195024193596937278095956235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130016129064624852063970823 195024193596937278095956235)
    ·
      refine ⟨292536290395405917143934353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195024193596937278095956235 292536290395405917143934353)
      ·
        refine ⟨219402217796554437857950765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292536290395405917143934353 219402217796554437857950765)
        ·
          refine ⟨82275831673707914196731537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 219402217796554437857950765 82275831673707914196731537)
          ·
            refine ⟨61706873755280935647548653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82275831673707914196731537 61706873755280935647548653)
            ·
              refine ⟨23140077658230350867830745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61706873755280935647548653 23140077658230350867830745)
              ·
                refine ⟨17355058243672763150873059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23140077658230350867830745 17355058243672763150873059)
                ·
                  refine ⟨26032587365509144726309589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17355058243672763150873059 26032587365509144726309589)
                  ·
                    refine ⟨610138766379120579522881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26032587365509144726309589 610138766379120579522881)
                    ·
                      rfl

theorem cell23_3564723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 7].length) (baseStart_3564723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3564723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3564723 prefixEnd_3564723 := by exact prefixLift 3564723
  have htrace : WordTrace (prefixWord ++ tailWord_3564723) baseStart_3564723 baseEnd_3564723 := by
    simpa [prefixWord, tailWord_3564723, baseEnd_3564723] using wordTrace_append hprefix tailTrace_3564723
  have hstable : (prefixWord ++ tailWord_3564723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564723).length < 2 ^ (prefixWord ++ tailWord_3564723).sum := by decide
  have hdescent : baseEnd_3564723 < baseStart_3564723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564757 : List Nat := [1, 3, 2, 4, 1, 2, 1, 2, 2, 5]
def baseStart_3564757 : Nat := 118140960795 + 3564757 * 2 ^ 59
def prefixEnd_3564757 : Nat := 4983230072969 + 3 ^ 40 * 3564757 * 2
def baseEnd_3564757 : Nat := 610144585826538201847829

theorem tailTrace_3564757 : CollatzResearch.WordTrace tailWord_3564757 prefixEnd_3564757 610144585826538201847829 := by
  unfold tailWord_3564757
  simp only [CollatzResearch.WordTrace]
  refine ⟨130017369146501675870708525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86678246097667783913805683 130017369146501675870708525)
  ·
    refine ⟨48756513429938128451515697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130017369146501675870708525 48756513429938128451515697)
    ·
      refine ⟨36567385072453596338636773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48756513429938128451515697 36567385072453596338636773)
      ·
        refine ⟨6856384701085049313494395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36567385072453596338636773 6856384701085049313494395)
        ·
          refine ⟨10284577051627573970241593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6856384701085049313494395 10284577051627573970241593)
          ·
            refine ⟨7713432788720680477681195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10284577051627573970241593 7713432788720680477681195)
            ·
              refine ⟨11570149183081020716521793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7713432788720680477681195 11570149183081020716521793)
              ·
                refine ⟨8677611887310765537391345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11570149183081020716521793 8677611887310765537391345)
                ·
                  refine ⟨6508208915483074153043509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8677611887310765537391345 6508208915483074153043509)
                  ·
                    refine ⟨610144585826538201847829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6508208915483074153043509 610144585826538201847829)
                    ·
                      rfl

theorem cell23_3564757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 2, 2, 5].length) (baseStart_3564757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3564757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3564757 prefixEnd_3564757 := by exact prefixLift 3564757
  have htrace : WordTrace (prefixWord ++ tailWord_3564757) baseStart_3564757 baseEnd_3564757 := by
    simpa [prefixWord, tailWord_3564757, baseEnd_3564757] using wordTrace_append hprefix tailTrace_3564757
  have hstable : (prefixWord ++ tailWord_3564757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564757).length < 2 ^ (prefixWord ++ tailWord_3564757).sum := by decide
  have hdescent : baseEnd_3564757 < baseStart_3564757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564790 : List Nat := [5, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6]
def baseStart_3564790 : Nat := 118140960795 + 3564790 * 2 ^ 59
def prefixEnd_3564790 : Nat := 4983230072969 + 3 ^ 40 * 3564790 * 2
def baseEnd_3564790 : Nat := 1830450702341212976430835

theorem tailTrace_3564790 : CollatzResearch.WordTrace tailWord_3564790 prefixEnd_3564790 1830450702341212976430835 := by
  unfold tailWord_3564790
  simp only [CollatzResearch.WordTrace]
  refine ⟨8126160797211382656666239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86679048503588081671106549 8126160797211382656666239)
  ·
    refine ⟨12189241195817073984999359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8126160797211382656666239 12189241195817073984999359)
    ·
      refine ⟨18283861793725610977499039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12189241195817073984999359 18283861793725610977499039)
      ·
        refine ⟨27425792690588416466248559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18283861793725610977499039 27425792690588416466248559)
        ·
          refine ⟨41138689035882624699372839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27425792690588416466248559 41138689035882624699372839)
          ·
            refine ⟨61708033553823937049059259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41138689035882624699372839 61708033553823937049059259)
            ·
              refine ⟨92562050330735905573588889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61708033553823937049059259 92562050330735905573588889)
              ·
                refine ⟨69421537748051929180191667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92562050330735905573588889 69421537748051929180191667)
                ·
                  refine ⟨104132306622077893770287501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69421537748051929180191667 104132306622077893770287501)
                  ·
                    refine ⟨39049614983279210163857813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 104132306622077893770287501 39049614983279210163857813)
                    ·
                      refine ⟨1830450702341212976430835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39049614983279210163857813 1830450702341212976430835)
                      ·
                        rfl

theorem cell23_3564790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_3564790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3564790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3564790 prefixEnd_3564790 := by exact prefixLift 3564790
  have htrace : WordTrace (prefixWord ++ tailWord_3564790) baseStart_3564790 baseEnd_3564790 := by
    simpa [prefixWord, tailWord_3564790, baseEnd_3564790] using wordTrace_append hprefix tailTrace_3564790
  have hstable : (prefixWord ++ tailWord_3564790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564790).length < 2 ^ (prefixWord ++ tailWord_3564790).sum := by decide
  have hdescent : baseEnd_3564790 < baseStart_3564790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564827 : List Nat := [1, 1, 1, 1, 1, 1, 5, 5, 3, 1, 3]
def baseStart_3564827 : Nat := 118140960795 + 3564827 * 2 ^ 59
def prefixEnd_3564827 : Nat := 4983230072969 + 3 ^ 40 * 3564827 * 2
def baseEnd_3564827 : Nat := 1830469701125429331668165

theorem tailTrace_3564827 : CollatzResearch.WordTrace tailWord_3564827 prefixEnd_3564827 1830469701125429331668165 := by
  unfold tailWord_3564827
  simp only [CollatzResearch.WordTrace]
  refine ⟨130019922256248077825756735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86679948170832051883837823 130019922256248077825756735)
  ·
    refine ⟨195029883384372116738635103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130019922256248077825756735 195029883384372116738635103)
    ·
      refine ⟨292544825076558175107952655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195029883384372116738635103 292544825076558175107952655)
      ·
        refine ⟨438817237614837262661928983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292544825076558175107952655 438817237614837262661928983)
        ·
          refine ⟨658225856422255893992893475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 438817237614837262661928983 658225856422255893992893475)
          ·
            refine ⟨987338784633383840989340213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 658225856422255893992893475 987338784633383840989340213)
            ·
              refine ⟨92563011059379735092750645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 987338784633383840989340213 92563011059379735092750645)
              ·
                refine ⟨8677782286816850164945373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92563011059379735092750645 8677782286816850164945373)
                ·
                  refine ⟨3254168357556318811854515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8677782286816850164945373 3254168357556318811854515)
                  ·
                    refine ⟨4881252536334478217781773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3254168357556318811854515 4881252536334478217781773)
                    ·
                      refine ⟨1830469701125429331668165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4881252536334478217781773 1830469701125429331668165)
                      ·
                        rfl

theorem cell23_3564827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 3, 1, 3].length) (baseStart_3564827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3564827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3564827 prefixEnd_3564827 := by exact prefixLift 3564827
  have htrace : WordTrace (prefixWord ++ tailWord_3564827) baseStart_3564827 baseEnd_3564827 := by
    simpa [prefixWord, tailWord_3564827, baseEnd_3564827] using wordTrace_append hprefix tailTrace_3564827
  have hstable : (prefixWord ++ tailWord_3564827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564827).length < 2 ^ (prefixWord ++ tailWord_3564827).sum := by decide
  have hdescent : baseEnd_3564827 < baseStart_3564827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564880 : List Nat := [2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 6]
def baseStart_3564880 : Nat := 118140960795 + 3564880 * 2 ^ 59
def prefixEnd_3564880 : Nat := 4983230072969 + 3 ^ 40 * 3564880 * 2
def baseEnd_3564880 : Nat := 1830496915600117624305421

theorem tailTrace_3564880 : CollatzResearch.WordTrace tailWord_3564880 prefixEnd_3564880 1830496915600117624305421 := by
  unfold tailWord_3564880
  simp only [CollatzResearch.WordTrace]
  refine ⟨65010927662528033938718047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86681236883370711918290729 65010927662528033938718047)
  ·
    refine ⟨97516391493792050908077071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65010927662528033938718047 97516391493792050908077071)
    ·
      refine ⟨146274587240688076362115607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97516391493792050908077071 146274587240688076362115607)
      ·
        refine ⟨219411880861032114543173411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146274587240688076362115607 219411880861032114543173411)
        ·
          refine ⟨329117821291548171814760117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219411880861032114543173411 329117821291548171814760117)
          ·
            refine ⟨30854795746082641107633761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 329117821291548171814760117 30854795746082641107633761)
            ·
              refine ⟨23141096809561980830725321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30854795746082641107633761 23141096809561980830725321)
              ·
                refine ⟨17355822607171485623043991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23141096809561980830725321 17355822607171485623043991)
                ·
                  refine ⟨26033733910757228434565987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17355822607171485623043991 26033733910757228434565987)
                  ·
                    refine ⟨39050600866135842651848981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26033733910757228434565987 39050600866135842651848981)
                    ·
                      refine ⟨1830496915600117624305421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39050600866135842651848981 1830496915600117624305421)
                      ·
                        rfl

theorem cell23_3564880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 6].length) (baseStart_3564880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3564880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3564880 prefixEnd_3564880 := by exact prefixLift 3564880
  have htrace : WordTrace (prefixWord ++ tailWord_3564880) baseStart_3564880 baseEnd_3564880 := by
    simpa [prefixWord, tailWord_3564880, baseEnd_3564880] using wordTrace_append hprefix tailTrace_3564880
  have hstable : (prefixWord ++ tailWord_3564880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564880).length < 2 ^ (prefixWord ++ tailWord_3564880).sum := by decide
  have hdescent : baseEnd_3564880 < baseStart_3564880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564887 : List Nat := [1, 1, 3, 2, 3, 3, 1, 2, 1, 1, 5]
def baseStart_3564887 : Nat := 118140960795 + 3564887 * 2 ^ 59
def prefixEnd_3564887 : Nat := 4983230072969 + 3 ^ 40 * 3564887 * 2
def baseEnd_3564887 : Nat := 1830500509964699096917889

theorem tailTrace_3564887 : CollatzResearch.WordTrace tailWord_3564887 prefixEnd_3564887 1830500509964699096917889 := by
  unfold tailWord_3564887
  simp only [CollatzResearch.WordTrace]
  refine ⟨130022110636030708072940915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86681407090687138715293943 130022110636030708072940915)
  ·
    refine ⟨195033165954046062109411373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130022110636030708072940915 195033165954046062109411373)
    ·
      refine ⟨73137437232767273291029265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195033165954046062109411373 73137437232767273291029265)
      ·
        refine ⟨54853077924575454968271949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73137437232767273291029265 54853077924575454968271949)
        ·
          refine ⟨20569904221715795613101981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54853077924575454968271949 20569904221715795613101981)
          ·
            refine ⟨7713714083143423354913243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20569904221715795613101981 7713714083143423354913243)
            ·
              refine ⟨11570571124715135032369865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7713714083143423354913243 11570571124715135032369865)
              ·
                refine ⟨8677928343536351274277399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11570571124715135032369865 8677928343536351274277399)
                ·
                  refine ⟨13016892515304526911416099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8677928343536351274277399 13016892515304526911416099)
                  ·
                    refine ⟨19525338772956790367124149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13016892515304526911416099 19525338772956790367124149)
                    ·
                      refine ⟨1830500509964699096917889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19525338772956790367124149 1830500509964699096917889)
                      ·
                        rfl

theorem cell23_3564887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 2, 1, 1, 5].length) (baseStart_3564887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3564887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3564887 prefixEnd_3564887 := by exact prefixLift 3564887
  have htrace : WordTrace (prefixWord ++ tailWord_3564887) baseStart_3564887 baseEnd_3564887 := by
    simpa [prefixWord, tailWord_3564887, baseEnd_3564887] using wordTrace_append hprefix tailTrace_3564887
  have hstable : (prefixWord ++ tailWord_3564887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564887).length < 2 ^ (prefixWord ++ tailWord_3564887).sum := by decide
  have hdescent : baseEnd_3564887 < baseStart_3564887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564935 : List Nat := [1, 1, 4, 2, 2, 3, 3, 2, 1, 2, 2]
def baseStart_3564935 : Nat := 118140960795 + 3564935 * 2 ^ 59
def prefixEnd_3564935 : Nat := 4983230072969 + 3 ^ 40 * 3564935 * 2
def baseEnd_3564935 : Nat := 1830525157036114909117669

theorem tailTrace_3564935 : CollatzResearch.WordTrace tailWord_3564935 prefixEnd_3564935 1830525157036114909117669 := by
  unfold tailWord_3564935
  simp only [CollatzResearch.WordTrace]
  refine ⟨130023861339856812270688259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86682574226571208180458839 130023861339856812270688259)
  ·
    refine ⟨195035792009785218406032389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130023861339856812270688259 195035792009785218406032389)
    ·
      refine ⟨36569211001834728451131073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195035792009785218406032389 36569211001834728451131073)
      ·
        refine ⟨27426908251376046338348305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36569211001834728451131073 27426908251376046338348305)
        ·
          refine ⟨20570181188532034753761229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27426908251376046338348305 20570181188532034753761229)
          ·
            refine ⟨7713817945699513032660461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20570181188532034753761229 7713817945699513032660461)
            ·
              refine ⟨2892681729637317387247673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7713817945699513032660461 2892681729637317387247673)
              ·
                refine ⟨2169511297227988040435755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2892681729637317387247673 2169511297227988040435755)
                ·
                  refine ⟨3254266945841982060653633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2169511297227988040435755 3254266945841982060653633)
                  ·
                    refine ⟨2440700209381486545490225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3254266945841982060653633 2440700209381486545490225)
                    ·
                      refine ⟨1830525157036114909117669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2440700209381486545490225 1830525157036114909117669)
                      ·
                        rfl

theorem cell23_3564935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 2, 1, 2, 2].length) (baseStart_3564935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3564935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3564935 prefixEnd_3564935 := by exact prefixLift 3564935
  have htrace : WordTrace (prefixWord ++ tailWord_3564935) baseStart_3564935 baseEnd_3564935 := by
    simpa [prefixWord, tailWord_3564935, baseEnd_3564935] using wordTrace_append hprefix tailTrace_3564935
  have hstable : (prefixWord ++ tailWord_3564935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564935).length < 2 ^ (prefixWord ++ tailWord_3564935).sum := by decide
  have hdescent : baseEnd_3564935 < baseStart_3564935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3564977 : List Nat := [1, 2, 2, 4, 1, 1, 1, 3, 2, 1, 5]
def baseStart_3564977 : Nat := 118140960795 + 3564977 * 2 ^ 59
def prefixEnd_3564977 : Nat := 4983230072969 + 3 ^ 40 * 3564977 * 2
def baseEnd_3564977 : Nat := 1830546723223603744792475

theorem tailTrace_3564977 : CollatzResearch.WordTrace tailWord_3564977 prefixEnd_3564977 1830546723223603744792475 := by
  unfold tailWord_3564977
  simp only [CollatzResearch.WordTrace]
  refine ⟨130025393205704653443717185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86683595470469768962478123 130025393205704653443717185)
  ·
    refine ⟨97519044904278490082787889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130025393205704653443717185 97519044904278490082787889)
    ·
      refine ⟨73139283678208867562090917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97519044904278490082787889 73139283678208867562090917)
      ·
        refine ⟨13713615689664162667892047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73139283678208867562090917 13713615689664162667892047)
        ·
          refine ⟨20570423534496244001838071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13713615689664162667892047 20570423534496244001838071)
          ·
            refine ⟨30855635301744366002757107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20570423534496244001838071 30855635301744366002757107)
            ·
              refine ⟨46283452952616549004135661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30855635301744366002757107 46283452952616549004135661)
              ·
                refine ⟨17356294857231205876550873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46283452952616549004135661 17356294857231205876550873)
                ·
                  refine ⟨13017221142923404407413155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17356294857231205876550873 13017221142923404407413155)
                  ·
                    refine ⟨19525831714385106611119733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13017221142923404407413155 19525831714385106611119733)
                    ·
                      refine ⟨1830546723223603744792475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19525831714385106611119733 1830546723223603744792475)
                      ·
                        rfl

theorem cell23_3564977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_3564977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3564977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3564977 prefixEnd_3564977 := by exact prefixLift 3564977
  have htrace : WordTrace (prefixWord ++ tailWord_3564977) baseStart_3564977 baseEnd_3564977 := by
    simpa [prefixWord, tailWord_3564977, baseEnd_3564977] using wordTrace_append hprefix tailTrace_3564977
  have hstable : (prefixWord ++ tailWord_3564977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3564977).length < 2 ^ (prefixWord ++ tailWord_3564977).sum := by decide
  have hdescent : baseEnd_3564977 < baseStart_3564977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3564977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565004 : List Nat := [2, 2, 1, 4, 2, 2, 1, 1, 2, 2, 4]
def baseStart_3565004 : Nat := 118140960795 + 3565004 * 2 ^ 59
def prefixEnd_3565004 : Nat := 4983230072969 + 3 ^ 40 * 3565004 * 2
def baseEnd_3565004 : Nat := 1830560587201275139154851

theorem tailTrace_3565004 : CollatzResearch.WordTrace tailWord_3565004 prefixEnd_3565004 1830560587201275139154851 := by
  unfold tailWord_3565004
  simp only [CollatzResearch.WordTrace]
  refine ⟨65013188988303418527475033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86684251984404558036633377 65013188988303418527475033)
  ·
    refine ⟨48759891741227563895606275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65013188988303418527475033 48759891741227563895606275)
    ·
      refine ⟨73139837611841345843409413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48759891741227563895606275 73139837611841345843409413)
      ·
        refine ⟨13713719552220252345639265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73139837611841345843409413 13713719552220252345639265)
        ·
          refine ⟨10285289664165189259229449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13713719552220252345639265 10285289664165189259229449)
          ·
            refine ⟨7713967248123891944422087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10285289664165189259229449 7713967248123891944422087)
            ·
              refine ⟨11570950872185837916633131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7713967248123891944422087 11570950872185837916633131)
              ·
                refine ⟨17356426308278756874949697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11570950872185837916633131 17356426308278756874949697)
                ·
                  refine ⟨13017319731209067656212273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17356426308278756874949697 13017319731209067656212273)
                  ·
                    refine ⟨9762989798406800742159205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13017319731209067656212273 9762989798406800742159205)
                    ·
                      refine ⟨1830560587201275139154851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9762989798406800742159205 1830560587201275139154851)
                      ·
                        rfl

theorem cell23_3565004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_3565004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3565004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3565004 prefixEnd_3565004 := by exact prefixLift 3565004
  have htrace : WordTrace (prefixWord ++ tailWord_3565004) baseStart_3565004 baseEnd_3565004 := by
    simpa [prefixWord, tailWord_3565004, baseEnd_3565004] using wordTrace_append hprefix tailTrace_3565004
  have hstable : (prefixWord ++ tailWord_3565004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565004).length < 2 ^ (prefixWord ++ tailWord_3565004).sum := by decide
  have hdescent : baseEnd_3565004 < baseStart_3565004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565007 : List Nat := [1, 1, 2, 1, 1, 4, 3, 1, 1, 5, 3]
def baseStart_3565007 : Nat := 118140960795 + 3565007 * 2 ^ 59
def prefixEnd_3565007 : Nat := 4983230072969 + 3 ^ 40 * 3565007 * 2
def baseEnd_3565007 : Nat := 1830562127643238627417337

theorem tailTrace_3565007 : CollatzResearch.WordTrace tailWord_3565007 prefixEnd_3565007 1830562127643238627417337 := by
  unfold tailWord_3565007
  simp only [CollatzResearch.WordTrace]
  refine ⟨130026487395595968567309275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86684324930397312378206183 130026487395595968567309275)
  ·
    refine ⟨195039731093393952850963913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130026487395595968567309275 195039731093393952850963913)
    ·
      refine ⟨146279798320045464638222935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195039731093393952850963913 146279798320045464638222935)
      ·
        refine ⟨219419697480068196957334403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146279798320045464638222935 219419697480068196957334403)
        ·
          refine ⟨329129546220102295436001605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219419697480068196957334403 329129546220102295436001605)
          ·
            refine ⟨61711789916269180394250301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 329129546220102295436001605 61711789916269180394250301)
            ·
              refine ⟨23141921218600942647843863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61711789916269180394250301 23141921218600942647843863)
              ·
                refine ⟨34712881827901413971765795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23141921218600942647843863 34712881827901413971765795)
                ·
                  refine ⟨52069322741852120957648693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34712881827901413971765795 52069322741852120957648693)
                  ·
                    refine ⟨4881499007048636339779565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52069322741852120957648693 4881499007048636339779565)
                    ·
                      refine ⟨1830562127643238627417337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4881499007048636339779565 1830562127643238627417337)
                      ·
                        rfl

theorem cell23_3565007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 5, 3].length) (baseStart_3565007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3565007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3565007 prefixEnd_3565007 := by exact prefixLift 3565007
  have htrace : WordTrace (prefixWord ++ tailWord_3565007) baseStart_3565007 baseEnd_3565007 := by
    simpa [prefixWord, tailWord_3565007, baseEnd_3565007] using wordTrace_append hprefix tailTrace_3565007
  have hstable : (prefixWord ++ tailWord_3565007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565007).length < 2 ^ (prefixWord ++ tailWord_3565007).sum := by decide
  have hdescent : baseEnd_3565007 < baseStart_3565007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565014 : List Nat := [5, 2, 1, 1, 1, 2, 1, 1, 9]
def baseStart_3565014 : Nat := 118140960795 + 3565014 * 2 ^ 59
def prefixEnd_3565014 : Nat := 4983230072969 + 3 ^ 40 * 3565014 * 2
def baseEnd_3565014 : Nat := 203396191334202233336645

theorem tailTrace_3565014 : CollatzResearch.WordTrace tailWord_3565014 prefixEnd_3565014 203396191334202233336645 := by
  unfold tailWord_3565014
  simp only [CollatzResearch.WordTrace]
  refine ⟨8126671419160663047675881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86684495137713739175209397 8126671419160663047675881)
  ·
    refine ⟨6095003564370497285756911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8126671419160663047675881 6095003564370497285756911)
    ·
      refine ⟨9142505346555745928635367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6095003564370497285756911 9142505346555745928635367)
      ·
        refine ⟨13713758019833618892953051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9142505346555745928635367 13713758019833618892953051)
        ·
          refine ⟨20570637029750428339429577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13713758019833618892953051 20570637029750428339429577)
          ·
            refine ⟨15427977772312821254572183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20570637029750428339429577 15427977772312821254572183)
            ·
              refine ⟨23141966658469231881858275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15427977772312821254572183 23141966658469231881858275)
              ·
                refine ⟨34712949987703847822787413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23141966658469231881858275 34712949987703847822787413)
                ·
                  refine ⟨203396191334202233336645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 34712949987703847822787413 203396191334202233336645)
                  ·
                    rfl

theorem cell23_3565014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_3565014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3565014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3565014 prefixEnd_3565014 := by exact prefixLift 3565014
  have htrace : WordTrace (prefixWord ++ tailWord_3565014) baseStart_3565014 baseEnd_3565014 := by
    simpa [prefixWord, tailWord_3565014, baseEnd_3565014] using wordTrace_append hprefix tailTrace_3565014
  have hstable : (prefixWord ++ tailWord_3565014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565014).length < 2 ^ (prefixWord ++ tailWord_3565014).sum := by decide
  have hdescent : baseEnd_3565014 < baseStart_3565014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565031 : List Nat := [1, 1, 5, 2, 1, 3, 2, 3, 5]
def baseStart_3565031 : Nat := 118140960795 + 3565031 * 2 ^ 59
def prefixEnd_3565031 : Nat := 4983230072969 + 3 ^ 40 * 3565031 * 2
def baseEnd_3565031 : Nat := 203397161242105170390803

theorem tailTrace_3565031 : CollatzResearch.WordTrace tailWord_3565031 prefixEnd_3565031 203397161242105170390803 := by
  unfold tailWord_3565031
  simp only [CollatzResearch.WordTrace]
  refine ⟨130027362747509020666182947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86684908498339347110788631 130027362747509020666182947)
  ·
    refine ⟨195041044121263530999274421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130027362747509020666182947 195041044121263530999274421)
    ·
      refine ⟨18285097886368456031181977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 195041044121263530999274421 18285097886368456031181977)
      ·
        refine ⟨13713823414776342023386483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18285097886368456031181977 13713823414776342023386483)
        ·
          refine ⟨20570735122164513035079725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13713823414776342023386483 20570735122164513035079725)
          ·
            refine ⟨7714025670811692388154897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20570735122164513035079725 7714025670811692388154897)
            ·
              refine ⟨5785519253108769291116173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7714025670811692388154897 5785519253108769291116173)
              ·
                refine ⟨2169569719915788484168565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5785519253108769291116173 2169569719915788484168565)
                ·
                  refine ⟨203397161242105170390803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2169569719915788484168565 203397161242105170390803)
                  ·
                    rfl

theorem cell23_3565031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 3, 5].length) (baseStart_3565031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3565031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3565031 prefixEnd_3565031 := by exact prefixLift 3565031
  have htrace : WordTrace (prefixWord ++ tailWord_3565031) baseStart_3565031 baseEnd_3565031 := by
    simpa [prefixWord, tailWord_3565031, baseEnd_3565031] using wordTrace_append hprefix tailTrace_3565031
  have hstable : (prefixWord ++ tailWord_3565031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565031).length < 2 ^ (prefixWord ++ tailWord_3565031).sum := by decide
  have hdescent : baseEnd_3565031 < baseStart_3565031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565084 : List Nat := [2, 2, 3, 1, 2, 1, 1, 3, 1, 4, 3]
def baseStart_3565084 : Nat := 118140960795 + 3565084 * 2 ^ 59
def prefixEnd_3565084 : Nat := 4983230072969 + 3 ^ 40 * 3565084 * 2
def baseEnd_3565084 : Nat := 1830601665653634826154483

theorem tailTrace_3565084 : CollatzResearch.WordTrace tailWord_3565084 prefixEnd_3565084 1830601665653634826154483 := by
  unfold tailWord_3565084
  simp only [CollatzResearch.WordTrace]
  refine ⟨65014647908158505358931153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86686197210878007145241537 65014647908158505358931153)
  ·
    refine ⟨48760985931118879019198365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65014647908158505358931153 48760985931118879019198365)
    ·
      refine ⟨18285369724169579632199387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48760985931118879019198365 18285369724169579632199387)
      ·
        refine ⟨27428054586254369448299081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18285369724169579632199387 27428054586254369448299081)
        ·
          refine ⟨20571040939690777086224311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27428054586254369448299081 20571040939690777086224311)
          ·
            refine ⟨30856561409536165629336467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20571040939690777086224311 30856561409536165629336467)
            ·
              refine ⟨46284842114304248444004701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30856561409536165629336467 46284842114304248444004701)
              ·
                refine ⟨17356815792864093166501763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46284842114304248444004701 17356815792864093166501763)
                ·
                  refine ⟨26035223689296139749752645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17356815792864093166501763 26035223689296139749752645)
                  ·
                    refine ⟨4881604441743026203078621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26035223689296139749752645 4881604441743026203078621)
                    ·
                      refine ⟨1830601665653634826154483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4881604441743026203078621 1830601665653634826154483)
                      ·
                        rfl

theorem cell23_3565084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_3565084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3565084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3565084 prefixEnd_3565084 := by exact prefixLift 3565084
  have htrace : WordTrace (prefixWord ++ tailWord_3565084) baseStart_3565084 baseEnd_3565084 := by
    simpa [prefixWord, tailWord_3565084, baseEnd_3565084] using wordTrace_append hprefix tailTrace_3565084
  have hstable : (prefixWord ++ tailWord_3565084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565084).length < 2 ^ (prefixWord ++ tailWord_3565084).sum := by decide
  have hdescent : baseEnd_3565084 < baseStart_3565084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565087 : List Nat := [1, 1, 2, 4, 1, 1, 3, 2, 8]
def baseStart_3565087 : Nat := 118140960795 + 3565087 * 2 ^ 59
def prefixEnd_3565087 : Nat := 4983230072969 + 3 ^ 40 * 3565087 * 2
def baseEnd_3565087 : Nat := 203400356232844257157441

theorem tailTrace_3565087 : CollatzResearch.WordTrace tailWord_3565087 prefixEnd_3565087 203400356232844257157441 := by
  unfold tailWord_3565087
  simp only [CollatzResearch.WordTrace]
  refine ⟨130029405235306142230221515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86686270156870761486814343 130029405235306142230221515)
  ·
    refine ⟨195044107852959213345332273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130029405235306142230221515 195044107852959213345332273)
    ·
      refine ⟨146283080889719410008999205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195044107852959213345332273 146283080889719410008999205)
      ·
        refine ⟨27428077666822389376687351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146283080889719410008999205 27428077666822389376687351)
        ·
          refine ⟨41142116500233584065031027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27428077666822389376687351 41142116500233584065031027)
          ·
            refine ⟨61713174750350376097546541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41142116500233584065031027 61713174750350376097546541)
            ·
              refine ⟨23142440531381391036579953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61713174750350376097546541 23142440531381391036579953)
              ·
                refine ⟨17356830398536043277434965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23142440531381391036579953 17356830398536043277434965)
                ·
                  refine ⟨203400356232844257157441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17356830398536043277434965 203400356232844257157441)
                  ·
                    rfl

theorem cell23_3565087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 8].length) (baseStart_3565087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3565087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3565087 prefixEnd_3565087 := by exact prefixLift 3565087
  have htrace : WordTrace (prefixWord ++ tailWord_3565087) baseStart_3565087 baseEnd_3565087 := by
    simpa [prefixWord, tailWord_3565087, baseEnd_3565087] using wordTrace_append hprefix tailTrace_3565087
  have hstable : (prefixWord ++ tailWord_3565087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565087).length < 2 ^ (prefixWord ++ tailWord_3565087).sum := by decide
  have hdescent : baseEnd_3565087 < baseStart_3565087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565181 : List Nat := [1, 4, 1, 1, 4, 2, 2, 1, 1, 6]
def baseStart_3565181 : Nat := 118140960795 + 3565181 * 2 ^ 59
def prefixEnd_3565181 : Nat := 4983230072969 + 3 ^ 40 * 3565181 * 2
def baseEnd_3565181 : Nat := 610217157759040315547179

theorem tailTrace_3565181 : CollatzResearch.WordTrace tailWord_3565181 prefixEnd_3565181 610217157759040315547179 := by
  unfold tailWord_3565181
  simp only [CollatzResearch.WordTrace]
  refine ⟨130032833696965596284143397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86688555797977064189428931 130032833696965596284143397)
  ·
    refine ⟨24381156318181049303276887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130032833696965596284143397 24381156318181049303276887)
    ·
      refine ⟨36571734477271573954915331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24381156318181049303276887 36571734477271573954915331)
      ·
        refine ⟨54857601715907360932372997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36571734477271573954915331 54857601715907360932372997)
        ·
          refine ⟨10285800321732630174819937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54857601715907360932372997 10285800321732630174819937)
          ·
            refine ⟨7714350241299472631114953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10285800321732630174819937 7714350241299472631114953)
            ·
              refine ⟨5785762680974604473336215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7714350241299472631114953 5785762680974604473336215)
              ·
                refine ⟨8678644021461906710004323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5785762680974604473336215 8678644021461906710004323)
                ·
                  refine ⟨13017966032192860065006485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8678644021461906710004323 13017966032192860065006485)
                  ·
                    refine ⟨610217157759040315547179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13017966032192860065006485 610217157759040315547179)
                    ·
                      rfl

theorem cell23_3565181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 1, 1, 6].length) (baseStart_3565181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3565181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3565181 prefixEnd_3565181 := by exact prefixLift 3565181
  have htrace : WordTrace (prefixWord ++ tailWord_3565181) baseStart_3565181 baseEnd_3565181 := by
    simpa [prefixWord, tailWord_3565181, baseEnd_3565181] using wordTrace_append hprefix tailTrace_3565181
  have hstable : (prefixWord ++ tailWord_3565181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565181).length < 2 ^ (prefixWord ++ tailWord_3565181).sum := by decide
  have hdescent : baseEnd_3565181 < baseStart_3565181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565191 : List Nat := [1, 1, 4, 2, 1, 3, 2, 1, 3, 2, 3]
def baseStart_3565191 : Nat := 118140960795 + 3565191 * 2 ^ 59
def prefixEnd_3565191 : Nat := 4983230072969 + 3 ^ 40 * 3565191 * 2
def baseEnd_3565191 : Nat := 1830656608083665907516491

theorem tailTrace_3565191 : CollatzResearch.WordTrace tailWord_3565191 prefixEnd_3565191 1830656608083665907516491 := by
  unfold tailWord_3565191
  simp only [CollatzResearch.WordTrace]
  refine ⟨130033198426929367992007427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86688798951286245328004951 130033198426929367992007427)
  ·
    refine ⟨195049797640394051988011141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130033198426929367992007427 195049797640394051988011141)
    ·
      refine ⟨36571837057573884747752089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195049797640394051988011141 36571837057573884747752089)
      ·
        refine ⟨27428877793180413560814067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36571837057573884747752089 27428877793180413560814067)
        ·
          refine ⟨41143316689770620341221101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27428877793180413560814067 41143316689770620341221101)
          ·
            refine ⟨15428743758663982627957913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41143316689770620341221101 15428743758663982627957913)
            ·
              refine ⟨11571557818997986970968435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15428743758663982627957913 11571557818997986970968435)
              ·
                refine ⟨17357336728496980456452653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11571557818997986970968435 17357336728496980456452653)
                ·
                  refine ⟨6509001273186367671169745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17357336728496980456452653 6509001273186367671169745)
                  ·
                    refine ⟨4881750954889775753377309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6509001273186367671169745 4881750954889775753377309)
                    ·
                      refine ⟨1830656608083665907516491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4881750954889775753377309 1830656608083665907516491)
                      ·
                        rfl

theorem cell23_3565191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_3565191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3565191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3565191 prefixEnd_3565191 := by exact prefixLift 3565191
  have htrace : WordTrace (prefixWord ++ tailWord_3565191) baseStart_3565191 baseEnd_3565191 := by
    simpa [prefixWord, tailWord_3565191, baseEnd_3565191] using wordTrace_append hprefix tailTrace_3565191
  have hstable : (prefixWord ++ tailWord_3565191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565191).length < 2 ^ (prefixWord ++ tailWord_3565191).sum := by decide
  have hdescent : baseEnd_3565191 < baseStart_3565191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565192 : List Nat := [2, 1, 3, 5, 1, 2, 1, 1, 2, 3, 2]
def baseStart_3565192 : Nat := 118140960795 + 3565192 * 2 ^ 59
def prefixEnd_3565192 : Nat := 4983230072969 + 3 ^ 40 * 3565192 * 2
def baseEnd_3565192 : Nat := 1830657121564320403603987

theorem tailTrace_3565192 : CollatzResearch.WordTrace tailWord_3565192 prefixEnd_3565192 1830657121564320403603987 := by
  unfold tailWord_3565192
  simp only [CollatzResearch.WordTrace]
  refine ⟨65016617449962872581396915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86688823266617163441862553 65016617449962872581396915)
  ·
    refine ⟨97524926174944308872095373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65016617449962872581396915 97524926174944308872095373)
    ·
      refine ⟨36571847315604115827035765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97524926174944308872095373 36571847315604115827035765)
      ·
        refine ⟨3428610685837885858784603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36571847315604115827035765 3428610685837885858784603)
        ·
          refine ⟨5142916028756828788176905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3428610685837885858784603 5142916028756828788176905)
          ·
            refine ⟨3857187021567621591132679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5142916028756828788176905 3857187021567621591132679)
            ·
              refine ⟨5785780532351432386699019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3857187021567621591132679 5785780532351432386699019)
              ·
                refine ⟨8678670798527148580048529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5785780532351432386699019 8678670798527148580048529)
                ·
                  refine ⟨6509003098895361435036397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8678670798527148580048529 6509003098895361435036397)
                  ·
                    refine ⟨2440876162085760538138649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6509003098895361435036397 2440876162085760538138649)
                    ·
                      refine ⟨1830657121564320403603987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2440876162085760538138649 1830657121564320403603987)
                      ·
                        rfl

theorem cell23_3565192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_3565192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3565192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3565192 prefixEnd_3565192 := by exact prefixLift 3565192
  have htrace : WordTrace (prefixWord ++ tailWord_3565192) baseStart_3565192 baseEnd_3565192 := by
    simpa [prefixWord, tailWord_3565192, baseEnd_3565192] using wordTrace_append hprefix tailTrace_3565192
  have hstable : (prefixWord ++ tailWord_3565192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565192).length < 2 ^ (prefixWord ++ tailWord_3565192).sum := by decide
  have hdescent : baseEnd_3565192 < baseStart_3565192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565202 : List Nat := [3, 2, 3, 1, 4, 1, 2, 1, 1, 5]
def baseStart_3565202 : Nat := 118140960795 + 3565202 * 2 ^ 59
def prefixEnd_3565202 : Nat := 4983230072969 + 3 ^ 40 * 3565202 * 2
def baseEnd_3565202 : Nat := 610220752123621788159647

theorem tailTrace_3565202 : CollatzResearch.WordTrace tailWord_3565202 prefixEnd_3565202 610220752123621788159647 := by
  unfold tailWord_3565202
  simp only [CollatzResearch.WordTrace]
  refine ⟨32508399907472379217664465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86689066419926344580438573 32508399907472379217664465)
  ·
    refine ⟨24381299930604284413248349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32508399907472379217664465 24381299930604284413248349)
    ·
      refine ⟨9142987473976606654968131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24381299930604284413248349 9142987473976606654968131)
      ·
        refine ⟨13714481210964909982452197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9142987473976606654968131 13714481210964909982452197)
        ·
          refine ⟨2571465227055920621709787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13714481210964909982452197 2571465227055920621709787)
          ·
            refine ⟨3857197840583880932564681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2571465227055920621709787 3857197840583880932564681)
            ·
              refine ⟨2892898380437910699423511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3857197840583880932564681 2892898380437910699423511)
              ·
                refine ⟨4339347570656866049135267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2892898380437910699423511 4339347570656866049135267)
                ·
                  refine ⟨6509021355985299073702901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4339347570656866049135267 6509021355985299073702901)
                  ·
                    refine ⟨610220752123621788159647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6509021355985299073702901 610220752123621788159647)
                    ·
                      rfl

theorem cell23_3565202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_3565202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3565202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3565202 prefixEnd_3565202 := by exact prefixLift 3565202
  have htrace : WordTrace (prefixWord ++ tailWord_3565202) baseStart_3565202 baseEnd_3565202 := by
    simpa [prefixWord, tailWord_3565202, baseEnd_3565202] using wordTrace_append hprefix tailTrace_3565202
  have hstable : (prefixWord ++ tailWord_3565202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565202).length < 2 ^ (prefixWord ++ tailWord_3565202).sum := by decide
  have hdescent : baseEnd_3565202 < baseStart_3565202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565208 : List Nat := [2, 1, 2, 4, 1, 3, 1, 3, 1, 2, 3]
def baseStart_3565208 : Nat := 118140960795 + 3565208 * 2 ^ 59
def prefixEnd_3565208 : Nat := 4983230072969 + 3 ^ 40 * 3565208 * 2
def baseEnd_3565208 : Nat := 1830665337254792341003913

theorem tailTrace_3565208 : CollatzResearch.WordTrace tailWord_3565208 prefixEnd_3565208 1830665337254792341003913 := by
  unfold tailWord_3565208
  simp only [CollatzResearch.WordTrace]
  refine ⟨65016909233933889947688139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86689212311911853263584185 65016909233933889947688139)
  ·
    refine ⟨97525363850900834921532209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65016909233933889947688139 97525363850900834921532209)
    ·
      refine ⟨73144022888175626191149157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97525363850900834921532209 73144022888175626191149157)
      ·
        refine ⟨13714504291532929910840467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73144022888175626191149157 13714504291532929910840467)
        ·
          refine ⟨20571756437299394866260701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13714504291532929910840467 20571756437299394866260701)
          ·
            refine ⟨7714408663987273074847763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20571756437299394866260701 7714408663987273074847763)
            ·
              refine ⟨11571612995980909612271645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7714408663987273074847763 11571612995980909612271645)
              ·
                refine ⟨4339354873492841104601867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11571612995980909612271645 4339354873492841104601867)
                ·
                  refine ⟨6509032310239261656902801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4339354873492841104601867 6509032310239261656902801)
                  ·
                    refine ⟨4881774232679446242677101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6509032310239261656902801 4881774232679446242677101)
                    ·
                      refine ⟨1830665337254792341003913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4881774232679446242677101 1830665337254792341003913)
                      ·
                        rfl

theorem cell23_3565208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_3565208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3565208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3565208 prefixEnd_3565208 := by exact prefixLift 3565208
  have htrace : WordTrace (prefixWord ++ tailWord_3565208) baseStart_3565208 baseEnd_3565208 := by
    simpa [prefixWord, tailWord_3565208, baseEnd_3565208] using wordTrace_append hprefix tailTrace_3565208
  have hstable : (prefixWord ++ tailWord_3565208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565208).length < 2 ^ (prefixWord ++ tailWord_3565208).sum := by decide
  have hdescent : baseEnd_3565208 < baseStart_3565208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565295 : List Nat := [1, 1, 2, 1, 5, 1, 3, 3, 2, 2, 2]
def baseStart_3565295 : Nat := 118140960795 + 3565295 * 2 ^ 59
def prefixEnd_3565295 : Nat := 4983230072969 + 3 ^ 40 * 3565295 * 2
def baseEnd_3565295 : Nat := 1830710010071733500616013

theorem tailTrace_3565295 : CollatzResearch.WordTrace tailWord_3565295 prefixEnd_3565295 1830710010071733500616013 := by
  unfold tailWord_3565295
  simp only [CollatzResearch.WordTrace]
  refine ⟨130036991618552593753793339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86691327745701729169195559 130036991618552593753793339)
  ·
    refine ⟨195055487427828890630690009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130036991618552593753793339 195055487427828890630690009)
    ·
      refine ⟨146291615570871667973017507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195055487427828890630690009 146291615570871667973017507)
      ·
        refine ⟨219437423356307501959526261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146291615570871667973017507 219437423356307501959526261)
        ·
          refine ⟨20572258439653828308705587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 219437423356307501959526261 20572258439653828308705587)
          ·
            refine ⟨30858387659480742463058381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20572258439653828308705587 30858387659480742463058381)
            ·
              refine ⟨11571895372305278423646893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30858387659480742463058381 11571895372305278423646893)
              ·
                refine ⟨4339460764614479408867585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11571895372305278423646893 4339460764614479408867585)
                ·
                  refine ⟨3254595573460859556650689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4339460764614479408867585 3254595573460859556650689)
                  ·
                    refine ⟨2440946680095644667488017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3254595573460859556650689 2440946680095644667488017)
                    ·
                      refine ⟨1830710010071733500616013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2440946680095644667488017 1830710010071733500616013)
                      ·
                        rfl

theorem cell23_3565295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 3, 2, 2, 2].length) (baseStart_3565295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3565295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3565295 prefixEnd_3565295 := by exact prefixLift 3565295
  have htrace : WordTrace (prefixWord ++ tailWord_3565295) baseStart_3565295 baseEnd_3565295 := by
    simpa [prefixWord, tailWord_3565295, baseEnd_3565295] using wordTrace_append hprefix tailTrace_3565295
  have hstable : (prefixWord ++ tailWord_3565295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565295).length < 2 ^ (prefixWord ++ tailWord_3565295).sum := by decide
  have hdescent : baseEnd_3565295 < baseStart_3565295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565335 : List Nat := [1, 1, 3, 4, 2, 1, 4, 2, 5]
def baseStart_3565335 : Nat := 118140960795 + 3565335 * 2 ^ 59
def prefixEnd_3565335 : Nat := 4983230072969 + 3 ^ 40 * 3565335 * 2
def baseEnd_3565335 : Nat := 203414505477545927123981

theorem tailTrace_3565335 : CollatzResearch.WordTrace tailWord_3565335 prefixEnd_3565335 203414505477545927123981 := by
  unfold tailWord_3565335
  simp only [CollatzResearch.WordTrace]
  refine ⟨130038450538407680585249459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86692300358938453723499639 130038450538407680585249459)
  ·
    refine ⟨195057675807611520877874189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130038450538407680585249459 195057675807611520877874189)
    ·
      refine ⟨73146628427854320329202821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195057675807611520877874189 73146628427854320329202821)
      ·
        refine ⟨13714992830222685061725529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73146628427854320329202821 13714992830222685061725529)
        ·
          refine ⟨10286244622667013796294147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13714992830222685061725529 10286244622667013796294147)
          ·
            refine ⟨15429366934000520694441221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10286244622667013796294147 15429366934000520694441221)
            ·
              refine ⟨2893006300125097630207729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15429366934000520694441221 2893006300125097630207729)
              ·
                refine ⟨2169754725093823222655797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2893006300125097630207729 2169754725093823222655797)
                ·
                  refine ⟨203414505477545927123981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2169754725093823222655797 203414505477545927123981)
                  ·
                    rfl

theorem cell23_3565335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 2, 5].length) (baseStart_3565335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3565335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3565335 prefixEnd_3565335 := by exact prefixLift 3565335
  have htrace : WordTrace (prefixWord ++ tailWord_3565335) baseStart_3565335 baseEnd_3565335 := by
    simpa [prefixWord, tailWord_3565335, baseEnd_3565335] using wordTrace_append hprefix tailTrace_3565335
  have hstable : (prefixWord ++ tailWord_3565335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565335).length < 2 ^ (prefixWord ++ tailWord_3565335).sum := by decide
  have hdescent : baseEnd_3565335 < baseStart_3565335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565338 : List Nat := [3, 1, 1, 3, 2, 2, 1, 1, 2, 5, 2]
def baseStart_3565338 : Nat := 118140960795 + 3565338 * 2 ^ 59
def prefixEnd_3565338 : Nat := 4983230072969 + 3 ^ 40 * 3565338 * 2
def baseEnd_3565338 : Nat := 1830732089739876832378315

theorem tailTrace_3565338 : CollatzResearch.WordTrace tailWord_3565338 prefixEnd_3565338 1830732089739876832378315 := by
  unfold tailWord_3565338
  simp only [CollatzResearch.WordTrace]
  refine ⟨32509639989349203024402167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86692373304931208065072445 32509639989349203024402167)
  ·
    refine ⟨48764459984023804536603251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32509639989349203024402167 48764459984023804536603251)
    ·
      refine ⟨73146689976035706804904877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48764459984023804536603251 73146689976035706804904877)
      ·
        refine ⟨27430008741013390051839329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73146689976035706804904877 27430008741013390051839329)
        ·
          refine ⟨20572506555760042538879497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27430008741013390051839329 20572506555760042538879497)
          ·
            refine ⟨15429379916820031904159623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20572506555760042538879497 15429379916820031904159623)
            ·
              refine ⟨23144069875230047856239435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15429379916820031904159623 23144069875230047856239435)
              ·
                refine ⟨34716104812845071784359153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23144069875230047856239435 34716104812845071784359153)
                ·
                  refine ⟨26037078609633803838269365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34716104812845071784359153 26037078609633803838269365)
                  ·
                    refine ⟨2440976119653169109837753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26037078609633803838269365 2440976119653169109837753)
                    ·
                      refine ⟨1830732089739876832378315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2440976119653169109837753 1830732089739876832378315)
                      ·
                        rfl

theorem cell23_3565338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 2, 5, 2].length) (baseStart_3565338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3565338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3565338 prefixEnd_3565338 := by exact prefixLift 3565338
  have htrace : WordTrace (prefixWord ++ tailWord_3565338) baseStart_3565338 baseEnd_3565338 := by
    simpa [prefixWord, tailWord_3565338, baseEnd_3565338] using wordTrace_append hprefix tailTrace_3565338
  have hstable : (prefixWord ++ tailWord_3565338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565338).length < 2 ^ (prefixWord ++ tailWord_3565338).sum := by decide
  have hdescent : baseEnd_3565338 < baseStart_3565338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565342 : List Nat := [4, 3, 2, 2, 1, 1, 1, 1, 2, 2, 4]
def baseStart_3565342 : Nat := 118140960795 + 3565342 * 2 ^ 59
def prefixEnd_3565342 : Nat := 4983230072969 + 3 ^ 40 * 3565342 * 2
def baseEnd_3565342 : Nat := 1830734143662494816728297

theorem tailTrace_3565342 : CollatzResearch.WordTrace tailWord_3565342 prefixEnd_3565342 1830734143662494816728297 := by
  unfold tailWord_3565342
  simp only [CollatzResearch.WordTrace]
  refine ⟨16254838231172790097594285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86692470566254880520502853 16254838231172790097594285)
  ·
    refine ⟨6095564336689796286597857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16254838231172790097594285 6095564336689796286597857)
    ·
      refine ⟨4571673252517347214948393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6095564336689796286597857 4571673252517347214948393)
      ·
        refine ⟨3428754939388010411211295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4571673252517347214948393 3428754939388010411211295)
        ·
          refine ⟨5143132409082015616816943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3428754939388010411211295 5143132409082015616816943)
          ·
            refine ⟨7714698613623023425225415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5143132409082015616816943 7714698613623023425225415)
            ·
              refine ⟨11572047920434535137838123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7714698613623023425225415 11572047920434535137838123)
              ·
                refine ⟨17358071880651802706757185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11572047920434535137838123 17358071880651802706757185)
                ·
                  refine ⟨13018553910488852030067889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17358071880651802706757185 13018553910488852030067889)
                  ·
                    refine ⟨9763915432866639022550917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13018553910488852030067889 9763915432866639022550917)
                    ·
                      refine ⟨1830734143662494816728297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9763915432866639022550917 1830734143662494816728297)
                      ·
                        rfl

theorem cell23_3565342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_3565342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3565342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3565342 prefixEnd_3565342 := by exact prefixLift 3565342
  have htrace : WordTrace (prefixWord ++ tailWord_3565342) baseStart_3565342 baseEnd_3565342 := by
    simpa [prefixWord, tailWord_3565342, baseEnd_3565342] using wordTrace_append hprefix tailTrace_3565342
  have hstable : (prefixWord ++ tailWord_3565342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565342).length < 2 ^ (prefixWord ++ tailWord_3565342).sum := by decide
  have hdescent : baseEnd_3565342 < baseStart_3565342 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565365 : List Nat := [1, 3, 3, 1, 4, 2, 1, 1, 2, 5]
def baseStart_3565365 : Nat := 118140960795 + 3565365 * 2 ^ 59
def prefixEnd_3565365 : Nat := 4983230072969 + 3 ^ 40 * 3565365 * 2
def baseEnd_3565365 : Nat := 610248651239182742246897

theorem tailTrace_3565365 : CollatzResearch.WordTrace tailWord_3565365 prefixEnd_3565365 610248651239182742246897 := by
  unfold tailWord_3565365
  simp only [CollatzResearch.WordTrace]
  refine ⟨130039544728298995708841549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86693029818865997139227699 130039544728298995708841549)
  ·
    refine ⟨48764829273112123390815581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130039544728298995708841549 48764829273112123390815581)
    ·
      refine ⟨18286810977417046271555843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48764829273112123390815581 18286810977417046271555843)
      ·
        refine ⟨27430216466125569407333765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18286810977417046271555843 27430216466125569407333765)
        ·
          refine ⟨5143165587398544263875081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27430216466125569407333765 5143165587398544263875081)
          ·
            refine ⟨3857374190548908197906311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5143165587398544263875081 3857374190548908197906311)
            ·
              refine ⟨5786061285823362296859467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3857374190548908197906311 5786061285823362296859467)
              ·
                refine ⟨8679091928735043445289201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5786061285823362296859467 8679091928735043445289201)
                ·
                  refine ⟨6509318946551282583966901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8679091928735043445289201 6509318946551282583966901)
                  ·
                    refine ⟨610248651239182742246897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6509318946551282583966901 610248651239182742246897)
                    ·
                      rfl

theorem cell23_3565365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_3565365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3565365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3565365 prefixEnd_3565365 := by exact prefixLift 3565365
  have htrace : WordTrace (prefixWord ++ tailWord_3565365) baseStart_3565365 baseEnd_3565365 := by
    simpa [prefixWord, tailWord_3565365, baseEnd_3565365] using wordTrace_append hprefix tailTrace_3565365
  have hstable : (prefixWord ++ tailWord_3565365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565365).length < 2 ^ (prefixWord ++ tailWord_3565365).sum := by decide
  have hdescent : baseEnd_3565365 < baseStart_3565365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565368 : List Nat := [2, 1, 2, 1, 3, 3, 3, 1, 2, 1, 4]
def baseStart_3565368 : Nat := 118140960795 + 3565368 * 2 ^ 59
def prefixEnd_3565368 : Nat := 4983230072969 + 3 ^ 40 * 3565368 * 2
def baseEnd_3565368 : Nat := 1830747494159511715003177

theorem tailTrace_3565368 : CollatzResearch.WordTrace tailWord_3565368 prefixEnd_3565368 1830747494159511715003177 := by
  unfold tailWord_3565368
  simp only [CollatzResearch.WordTrace]
  refine ⟨65019827073644063610600379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86693102764858751480800505 65019827073644063610600379)
  ·
    refine ⟨97529740610466095415900569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65019827073644063610600379 97529740610466095415900569)
    ·
      refine ⟨73147305457849571561925427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97529740610466095415900569 73147305457849571561925427)
      ·
        refine ⟨109720958186774357342888141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73147305457849571561925427 109720958186774357342888141)
        ·
          refine ⟨41145359320040384003583053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109720958186774357342888141 41145359320040384003583053)
          ·
            refine ⟨15429509745015144001343645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41145359320040384003583053 15429509745015144001343645)
            ·
              refine ⟨5786066154380679000503867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15429509745015144001343645 5786066154380679000503867)
              ·
                refine ⟨8679099231571018500755801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5786066154380679000503867 8679099231571018500755801)
                ·
                  refine ⟨6509324423678263875566851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8679099231571018500755801 6509324423678263875566851)
                  ·
                    refine ⟨9763986635517395813350277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6509324423678263875566851 9763986635517395813350277)
                    ·
                      refine ⟨1830747494159511715003177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9763986635517395813350277 1830747494159511715003177)
                      ·
                        rfl

theorem cell23_3565368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 1, 2, 1, 4].length) (baseStart_3565368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3565368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3565368 prefixEnd_3565368 := by exact prefixLift 3565368
  have htrace : WordTrace (prefixWord ++ tailWord_3565368) baseStart_3565368 baseEnd_3565368 := by
    simpa [prefixWord, tailWord_3565368, baseEnd_3565368] using wordTrace_append hprefix tailTrace_3565368
  have hstable : (prefixWord ++ tailWord_3565368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565368).length < 2 ^ (prefixWord ++ tailWord_3565368).sum := by decide
  have hdescent : baseEnd_3565368 < baseStart_3565368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565445 : List Nat := [1, 3, 1, 1, 3, 2, 3, 2, 2, 3, 2]
def baseStart_3565445 : Nat := 118140960795 + 3565445 * 2 ^ 59
def prefixEnd_3565445 : Nat := 4983230072969 + 3 ^ 40 * 3565445 * 2
def baseEnd_3565445 : Nat := 1830787032169907913740323

theorem tailTrace_3565445 : CollatzResearch.WordTrace tailWord_3565445 prefixEnd_3565445 1830787032169907913740323 := by
  unfold tailWord_3565445
  simp only [CollatzResearch.WordTrace]
  refine ⟨130042462568009169371753789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86694975045339446247835859 130042462568009169371753789)
  ·
    refine ⟨48765923463003438514407671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130042462568009169371753789 48765923463003438514407671)
    ·
      refine ⟨73148885194505157771611507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48765923463003438514407671 73148885194505157771611507)
      ·
        refine ⟨109723327791757736657417261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73148885194505157771611507 109723327791757736657417261)
        ·
          refine ⟨41146247921909151246531473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109723327791757736657417261 41146247921909151246531473)
          ·
            refine ⟨30859685941431863434898605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41146247921909151246531473 30859685941431863434898605)
            ·
              refine ⟨11572382228036948788086977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30859685941431863434898605 11572382228036948788086977)
              ·
                refine ⟨8679286671027711591065233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11572382228036948788086977 8679286671027711591065233)
                ·
                  refine ⟨6509465003270783693298925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8679286671027711591065233 6509465003270783693298925)
                  ·
                    refine ⟨2441049376226543884987097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6509465003270783693298925 2441049376226543884987097)
                    ·
                      refine ⟨1830787032169907913740323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2441049376226543884987097 1830787032169907913740323)
                      ·
                        rfl

theorem cell23_3565445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2, 2, 3, 2].length) (baseStart_3565445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3565445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3565445 prefixEnd_3565445 := by exact prefixLift 3565445
  have htrace : WordTrace (prefixWord ++ tailWord_3565445) baseStart_3565445 baseEnd_3565445 := by
    simpa [prefixWord, tailWord_3565445, baseEnd_3565445] using wordTrace_append hprefix tailTrace_3565445
  have hstable : (prefixWord ++ tailWord_3565445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565445).length < 2 ^ (prefixWord ++ tailWord_3565445).sum := by decide
  have hdescent : baseEnd_3565445 < baseStart_3565445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565475 : List Nat := [1, 1, 1, 4, 1, 2, 1, 3, 5, 2, 2]
def baseStart_3565475 : Nat := 118140960795 + 3565475 * 2 ^ 59
def prefixEnd_3565475 : Nat := 4983230072969 + 3 ^ 40 * 3565475 * 2
def baseEnd_3565475 : Nat := 1830802436589542796365185

theorem tailTrace_3565475 : CollatzResearch.WordTrace tailWord_3565475 prefixEnd_3565475 1830802436589542796365185 := by
  unfold tailWord_3565475
  simp only [CollatzResearch.WordTrace]
  refine ⟨130043556757900484495345879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86695704505266989663563919 130043556757900484495345879)
  ·
    refine ⟨195065335136850726743018819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130043556757900484495345879 195065335136850726743018819)
    ·
      refine ⟨292598002705276090114528229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195065335136850726743018819 292598002705276090114528229)
      ·
        refine ⟨54862125507239266896474043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 292598002705276090114528229 54862125507239266896474043)
        ·
          refine ⟨82293188260858900344711065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54862125507239266896474043 82293188260858900344711065)
          ·
            refine ⟨61719891195644175258533299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82293188260858900344711065 61719891195644175258533299)
            ·
              refine ⟨92579836793466262887799949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61719891195644175258533299 92579836793466262887799949)
              ·
                refine ⟨34717438797549848582924981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92579836793466262887799949 34717438797549848582924981)
                ·
                  refine ⟨3254759887270298304649217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34717438797549848582924981 3254759887270298304649217)
                  ·
                    refine ⟨2441069915452723728486913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3254759887270298304649217 2441069915452723728486913)
                    ·
                      refine ⟨1830802436589542796365185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2441069915452723728486913 1830802436589542796365185)
                      ·
                        rfl

theorem cell23_3565475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 5, 2, 2].length) (baseStart_3565475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3565475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3565475 prefixEnd_3565475 := by exact prefixLift 3565475
  have htrace : WordTrace (prefixWord ++ tailWord_3565475) baseStart_3565475 baseEnd_3565475 := by
    simpa [prefixWord, tailWord_3565475, baseEnd_3565475] using wordTrace_append hprefix tailTrace_3565475
  have hstable : (prefixWord ++ tailWord_3565475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565475).length < 2 ^ (prefixWord ++ tailWord_3565475).sum := by decide
  have hdescent : baseEnd_3565475 < baseStart_3565475 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565502 : List Nat := [4, 2, 1, 1, 1, 4, 2, 2, 2, 4]
def baseStart_3565502 : Nat := 118140960795 + 3565502 * 2 ^ 59
def prefixEnd_3565502 : Nat := 4983230072969 + 3 ^ 40 * 3565502 * 2
def baseEnd_3565502 : Nat := 610272100189071396909187

theorem tailTrace_3565502 : CollatzResearch.WordTrace tailWord_3565502 prefixEnd_3565502 610272100189071396909187 := by
  unfold tailWord_3565502
  simp only [CollatzResearch.WordTrace]
  refine ⟨16255567691100333513322345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86696361019201778737719173 16255567691100333513322345)
  ·
    refine ⟨12191675768325250134991759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16255567691100333513322345 12191675768325250134991759)
    ·
      refine ⟨18287513652487875202487639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12191675768325250134991759 18287513652487875202487639)
      ·
        refine ⟨27431270478731812803731459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18287513652487875202487639 27431270478731812803731459)
        ·
          refine ⟨41146905718097719205597189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27431270478731812803731459 41146905718097719205597189)
          ·
            refine ⟨7715044822143322351049473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41146905718097719205597189 7715044822143322351049473)
            ·
              refine ⟨5786283616607491763287105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7715044822143322351049473 5786283616607491763287105)
              ·
                refine ⟨4339712712455618822465329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5786283616607491763287105 4339712712455618822465329)
                ·
                  refine ⟨3254784534341714116848997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4339712712455618822465329 3254784534341714116848997)
                  ·
                    refine ⟨610272100189071396909187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3254784534341714116848997 610272100189071396909187)
                    ·
                      rfl

theorem cell23_3565502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_3565502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3565502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3565502 prefixEnd_3565502 := by exact prefixLift 3565502
  have htrace : WordTrace (prefixWord ++ tailWord_3565502) baseStart_3565502 baseEnd_3565502 := by
    simpa [prefixWord, tailWord_3565502, baseEnd_3565502] using wordTrace_append hprefix tailTrace_3565502
  have hstable : (prefixWord ++ tailWord_3565502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565502).length < 2 ^ (prefixWord ++ tailWord_3565502).sum := by decide
  have hdescent : baseEnd_3565502 < baseStart_3565502 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565522 : List Nat := [3, 2, 2, 3, 2, 1, 2, 1, 1, 2, 4]
def baseStart_3565522 : Nat := 118140960795 + 3565522 * 2 ^ 59
def prefixEnd_3565522 : Nat := 4983230072969 + 3 ^ 40 * 3565522 * 2
def baseEnd_3565522 : Nat := 1830826570180304112477469

theorem tailTrace_3565522 : CollatzResearch.WordTrace tailWord_3565522 prefixEnd_3565522 1830826570180304112477469 := by
  unfold tailWord_3565522
  simp only [CollatzResearch.WordTrace]
  refine ⟨32511317747182552880576705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86696847325820141014871213 32511317747182552880576705)
  ·
    refine ⟨24383488310386914660432529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32511317747182552880576705 24383488310386914660432529)
    ·
      refine ⟨18287616232790185995324397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24383488310386914660432529 18287616232790185995324397)
      ·
        refine ⟨6857856087296319748246649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18287616232790185995324397 6857856087296319748246649)
        ·
          refine ⟨5143392065472239811184987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6857856087296319748246649 5143392065472239811184987)
          ·
            refine ⟨7715088098208359716777481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5143392065472239811184987 7715088098208359716777481)
            ·
              refine ⟨5786316073656269787583111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7715088098208359716777481 5786316073656269787583111)
              ·
                refine ⟨8679474110484404681374667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5786316073656269787583111 8679474110484404681374667)
                ·
                  refine ⟨13019211165726607022062001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8679474110484404681374667 13019211165726607022062001)
                  ·
                    refine ⟨9764408374294955266546501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13019211165726607022062001 9764408374294955266546501)
                    ·
                      refine ⟨1830826570180304112477469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9764408374294955266546501 1830826570180304112477469)
                      ·
                        rfl

theorem cell23_3565522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_3565522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3565522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3565522 prefixEnd_3565522 := by exact prefixLift 3565522
  have htrace : WordTrace (prefixWord ++ tailWord_3565522) baseStart_3565522 baseEnd_3565522 := by
    simpa [prefixWord, tailWord_3565522, baseEnd_3565522] using wordTrace_append hprefix tailTrace_3565522
  have hstable : (prefixWord ++ tailWord_3565522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565522).length < 2 ^ (prefixWord ++ tailWord_3565522).sum := by decide
  have hdescent : baseEnd_3565522 < baseStart_3565522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565525 : List Nat := [1, 3, 2, 3, 2, 1, 1, 3, 1, 3, 3]
def baseStart_3565525 : Nat := 118140960795 + 3565525 * 2 ^ 59
def prefixEnd_3565525 : Nat := 4983230072969 + 3 ^ 40 * 3565525 * 2
def baseEnd_3565525 : Nat := 1830828110622267600739955

theorem tailTrace_3565525 : CollatzResearch.WordTrace tailWord_3565525 prefixEnd_3565525 1830828110622267600739955 := by
  unfold tailWord_3565525
  simp only [CollatzResearch.WordTrace]
  refine ⟨130045380407719343034666029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86696920271812895356444019 130045380407719343034666029)
  ·
    refine ⟨48767017652894753637999761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130045380407719343034666029 48767017652894753637999761)
    ·
      refine ⟨36575263239671065228499821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48767017652894753637999761 36575263239671065228499821)
      ·
        refine ⟨13715723714876649460687433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36575263239671065228499821 13715723714876649460687433)
        ·
          refine ⟨10286792786157487095515575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13715723714876649460687433 10286792786157487095515575)
          ·
            refine ⟨15430189179236230643273363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10286792786157487095515575 15430189179236230643273363)
            ·
              refine ⟨23145283768854345964910045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15430189179236230643273363 23145283768854345964910045)
              ·
                refine ⟨8679481413320379736841267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23145283768854345964910045 8679481413320379736841267)
                ·
                  refine ⟨13019222119980569605261901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8679481413320379736841267 13019222119980569605261901)
                  ·
                    refine ⟨4882208294992713601973213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13019222119980569605261901 4882208294992713601973213)
                    ·
                      refine ⟨1830828110622267600739955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4882208294992713601973213 1830828110622267600739955)
                      ·
                        rfl

theorem cell23_3565525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_3565525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3565525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3565525 prefixEnd_3565525 := by exact prefixLift 3565525
  have htrace : WordTrace (prefixWord ++ tailWord_3565525) baseStart_3565525 baseEnd_3565525 := by
    simpa [prefixWord, tailWord_3565525, baseEnd_3565525] using wordTrace_append hprefix tailTrace_3565525
  have hstable : (prefixWord ++ tailWord_3565525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565525).length < 2 ^ (prefixWord ++ tailWord_3565525).sum := by decide
  have hdescent : baseEnd_3565525 < baseStart_3565525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565526 : List Nat := [5, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2]
def baseStart_3565526 : Nat := 118140960795 + 3565526 * 2 ^ 59
def prefixEnd_3565526 : Nat := 4983230072969 + 3 ^ 40 * 3565526 * 2
def baseEnd_3565526 : Nat := 1830828624102922096827451

theorem tailTrace_3565526 : CollatzResearch.WordTrace tailWord_3565526 prefixEnd_3565526 1830828624102922096827451 := by
  unfold tailWord_3565526
  simp only [CollatzResearch.WordTrace]
  refine ⟨8127838555044732512840777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86696944587143813470301621 8127838555044732512840777)
  ·
    refine ⟨6095878916283549384630583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8127838555044732512840777 6095878916283549384630583)
    ·
      refine ⟨9143818374425324076945875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6095878916283549384630583 9143818374425324076945875)
      ·
        refine ⟨13715727561637986115418813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9143818374425324076945875 13715727561637986115418813)
        ·
          refine ⟨5143397835614244793282055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13715727561637986115418813 5143397835614244793282055)
          ·
            refine ⟨7715096753421367189923083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5143397835614244793282055 7715096753421367189923083)
            ·
              refine ⟨11572645130132050784884625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7715096753421367189923083 11572645130132050784884625)
              ·
                refine ⟨8679483847599038088663469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11572645130132050784884625 8679483847599038088663469)
                ·
                  refine ⟨3254806442849639283248801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8679483847599038088663469 3254806442849639283248801)
                  ·
                    refine ⟨2441104832137229462436601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3254806442849639283248801 2441104832137229462436601)
                    ·
                      refine ⟨1830828624102922096827451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2441104832137229462436601 1830828624102922096827451)
                      ·
                        rfl

theorem cell23_3565526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_3565526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3565526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3565526 prefixEnd_3565526 := by exact prefixLift 3565526
  have htrace : WordTrace (prefixWord ++ tailWord_3565526) baseStart_3565526 baseEnd_3565526 := by
    simpa [prefixWord, tailWord_3565526, baseEnd_3565526] using wordTrace_append hprefix tailTrace_3565526
  have hstable : (prefixWord ++ tailWord_3565526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565526).length < 2 ^ (prefixWord ++ tailWord_3565526).sum := by decide
  have hdescent : baseEnd_3565526 < baseStart_3565526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565565 : List Nat := [1, 4, 1, 1, 1, 2, 2, 2, 3, 4, 2]
def baseStart_3565565 : Nat := 118140960795 + 3565565 * 2 ^ 59
def prefixEnd_3565565 : Nat := 4983230072969 + 3 ^ 40 * 3565565 * 2
def baseEnd_3565565 : Nat := 1830848649848447444239771

theorem tailTrace_3565565 : CollatzResearch.WordTrace tailWord_3565565 prefixEnd_3565565 1830848649848447444239771 := by
  unfold tailWord_3565565
  simp only [CollatzResearch.WordTrace]
  refine ⟨130046839327574429866122149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86697892885049619910748099 130046839327574429866122149)
  ·
    refine ⟨24383782373920205599897903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130046839327574429866122149 24383782373920205599897903)
    ·
      refine ⟨36575673560880308399846855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24383782373920205599897903 36575673560880308399846855)
      ·
        refine ⟨54863510341320462599770283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36575673560880308399846855 54863510341320462599770283)
        ·
          refine ⟨82295265511980693899655425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54863510341320462599770283 82295265511980693899655425)
          ·
            refine ⟨61721449133985520424741569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82295265511980693899655425 61721449133985520424741569)
            ·
              refine ⟨46291086850489140318556177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61721449133985520424741569 46291086850489140318556177)
              ·
                refine ⟨34718315137866855238917133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46291086850489140318556177 34718315137866855238917133)
                ·
                  refine ⟨13019368176700070714593925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34718315137866855238917133 13019368176700070714593925)
                  ·
                    refine ⟨2441131533131263258986361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13019368176700070714593925 2441131533131263258986361)
                    ·
                      refine ⟨1830848649848447444239771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2441131533131263258986361 1830848649848447444239771)
                      ·
                        rfl

theorem cell23_3565565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3, 4, 2].length) (baseStart_3565565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3565565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3565565 prefixEnd_3565565 := by exact prefixLift 3565565
  have htrace : WordTrace (prefixWord ++ tailWord_3565565) baseStart_3565565 baseEnd_3565565 := by
    simpa [prefixWord, tailWord_3565565, baseEnd_3565565] using wordTrace_append hprefix tailTrace_3565565
  have hstable : (prefixWord ++ tailWord_3565565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565565).length < 2 ^ (prefixWord ++ tailWord_3565565).sum := by decide
  have hdescent : baseEnd_3565565 < baseStart_3565565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565568 : List Nat := [2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 3]
def baseStart_3565568 : Nat := 118140960795 + 3565568 * 2 ^ 59
def prefixEnd_3565568 : Nat := 4983230072969 + 3 ^ 40 * 3565568 * 2
def baseEnd_3565568 : Nat := 1830850190290410932502257

theorem tailTrace_3565568 : CollatzResearch.WordTrace tailWord_3565568 prefixEnd_3565568 1830850190290410932502257 := by
  unfold tailWord_3565568
  simp only [CollatzResearch.WordTrace]
  refine ⟨65023474373281780689240679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86697965831042374252320905 65023474373281780689240679)
  ·
    refine ⟨97535211559922671033861019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65023474373281780689240679 97535211559922671033861019)
    ·
      refine ⟨146302817339884006550791529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97535211559922671033861019 146302817339884006550791529)
      ·
        refine ⟨109727113004913004913093647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146302817339884006550791529 109727113004913004913093647)
        ·
          refine ⟨164590669507369507369640471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109727113004913004913093647 164590669507369507369640471)
          ·
            refine ⟨246886004261054261054460707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164590669507369507369640471 246886004261054261054460707)
            ·
              refine ⟨370329006391581391581691061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246886004261054261054460707 370329006391581391581691061)
              ·
                refine ⟨34718344349210755460783537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 370329006391581391581691061 34718344349210755460783537)
                ·
                  refine ⟨26038758261908066595587653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34718344349210755460783537 26038758261908066595587653)
                  ·
                    refine ⟨4882267174107762486672685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26038758261908066595587653 4882267174107762486672685)
                    ·
                      refine ⟨1830850190290410932502257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4882267174107762486672685 1830850190290410932502257)
                      ·
                        rfl

theorem cell23_3565568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 3].length) (baseStart_3565568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3565568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3565568 prefixEnd_3565568 := by exact prefixLift 3565568
  have htrace : WordTrace (prefixWord ++ tailWord_3565568) baseStart_3565568 baseEnd_3565568 := by
    simpa [prefixWord, tailWord_3565568, baseEnd_3565568] using wordTrace_append hprefix tailTrace_3565568
  have hstable : (prefixWord ++ tailWord_3565568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565568).length < 2 ^ (prefixWord ++ tailWord_3565568).sum := by decide
  have hdescent : baseEnd_3565568 < baseStart_3565568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565633 : List Nat := [1, 2, 5, 1, 2, 3, 2, 1, 2, 2, 2]
def baseStart_3565633 : Nat := 118140960795 + 3565633 * 2 ^ 59
def prefixEnd_3565633 : Nat := 4983230072969 + 3 ^ 40 * 3565633 * 2
def baseEnd_3565633 : Nat := 1830883566532953178189459

theorem tailTrace_3565633 : CollatzResearch.WordTrace tailWord_3565633 prefixEnd_3565633 1830883566532953178189459 := by
  unfold tailWord_3565633
  simp only [CollatzResearch.WordTrace]
  refine ⟨130049319491328077479597553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86699546327552051653065035 130049319491328077479597553)
  ·
    refine ⟨97536989618496058109698165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130049319491328077479597553 97536989618496058109698165)
    ·
      refine ⟨9144092776734005447784203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97536989618496058109698165 9144092776734005447784203)
      ·
        refine ⟨13716139165101008171676305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9144092776734005447784203 13716139165101008171676305)
        ·
          refine ⟨10287104373825756128757229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13716139165101008171676305 10287104373825756128757229)
          ·
            refine ⟨3857664140184658548283961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10287104373825756128757229 3857664140184658548283961)
            ·
              refine ⟨2893248105138493911212971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3857664140184658548283961 2893248105138493911212971)
              ·
                refine ⟨4339872157707740866819457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2893248105138493911212971 4339872157707740866819457)
                ·
                  refine ⟨3254904118280805650114593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4339872157707740866819457 3254904118280805650114593)
                  ·
                    refine ⟨2441178088710604237585945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3254904118280805650114593 2441178088710604237585945)
                    ·
                      refine ⟨1830883566532953178189459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2441178088710604237585945 1830883566532953178189459)
                      ·
                        rfl

theorem cell23_3565633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_3565633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3565633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3565633 prefixEnd_3565633 := by exact prefixLift 3565633
  have htrace : WordTrace (prefixWord ++ tailWord_3565633) baseStart_3565633 baseEnd_3565633 := by
    simpa [prefixWord, tailWord_3565633, baseEnd_3565633] using wordTrace_append hprefix tailTrace_3565633
  have hstable : (prefixWord ++ tailWord_3565633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565633).length < 2 ^ (prefixWord ++ tailWord_3565633).sum := by decide
  have hdescent : baseEnd_3565633 < baseStart_3565633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565645 : List Nat := [1, 6, 1, 1, 1, 1, 1, 2, 1, 1, 7]
def baseStart_3565645 : Nat := 118140960795 + 3565645 * 2 ^ 59
def prefixEnd_3565645 : Nat := 4983230072969 + 3 ^ 40 * 3565645 * 2
def baseEnd_3565645 : Nat := 1830889728300807131239403

theorem tailTrace_3565645 : CollatzResearch.WordTrace tailWord_3565645 prefixEnd_3565645 1830889728300807131239403 := by
  unfold tailWord_3565645
  simp only [CollatzResearch.WordTrace]
  refine ⟨130049757167284603529034389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86699838111523069019356259 130049757167284603529034389)
  ·
    refine ⟨6096082367216465790423487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 130049757167284603529034389 6096082367216465790423487)
    ·
      refine ⟨9144123550824698685635231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6096082367216465790423487 9144123550824698685635231)
      ·
        refine ⟨13716185326237048028452847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9144123550824698685635231 13716185326237048028452847)
        ·
          refine ⟨20574277989355572042679271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13716185326237048028452847 20574277989355572042679271)
          ·
            refine ⟨30861416984033358064018907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20574277989355572042679271 30861416984033358064018907)
            ·
              refine ⟨46292125476050037096028361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30861416984033358064018907 46292125476050037096028361)
              ·
                refine ⟨34719094107037527822021271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46292125476050037096028361 34719094107037527822021271)
                ·
                  refine ⟨52078641160556291733031907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34719094107037527822021271 52078641160556291733031907)
                  ·
                    refine ⟨78117961740834437599547861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52078641160556291733031907 78117961740834437599547861)
                    ·
                      refine ⟨1830889728300807131239403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 78117961740834437599547861 1830889728300807131239403)
                      ·
                        rfl

theorem cell23_3565645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_3565645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3565645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3565645 prefixEnd_3565645 := by exact prefixLift 3565645
  have htrace : WordTrace (prefixWord ++ tailWord_3565645) baseStart_3565645 baseEnd_3565645 := by
    simpa [prefixWord, tailWord_3565645, baseEnd_3565645] using wordTrace_append hprefix tailTrace_3565645
  have hstable : (prefixWord ++ tailWord_3565645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565645).length < 2 ^ (prefixWord ++ tailWord_3565645).sum := by decide
  have hdescent : baseEnd_3565645 < baseStart_3565645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565655 : List Nat := [1, 1, 3, 2, 2, 1, 3, 3, 2, 1, 4]
def baseStart_3565655 : Nat := 118140960795 + 3565655 * 2 ^ 59
def prefixEnd_3565655 : Nat := 4983230072969 + 3 ^ 40 * 3565655 * 2
def baseEnd_3565655 : Nat := 1830894863107352092114357

theorem tailTrace_3565655 : CollatzResearch.WordTrace tailWord_3565655 prefixEnd_3565655 1830894863107352092114357 := by
  unfold tailWord_3565655
  simp only [CollatzResearch.WordTrace]
  refine ⟨130050121897248375236898419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86700081264832250157932279 130050121897248375236898419)
  ·
    refine ⟨195075182845872562855347629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130050121897248375236898419 195075182845872562855347629)
    ·
      refine ⟨73153193567202211070755361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195075182845872562855347629 73153193567202211070755361)
      ·
        refine ⟨54864895175401658303066521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73153193567202211070755361 54864895175401658303066521)
        ·
          refine ⟨41148671381551243727299891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54864895175401658303066521 41148671381551243727299891)
          ·
            refine ⟨61723007072326865590949837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41148671381551243727299891 61723007072326865590949837)
            ·
              refine ⟨23146127652122574596606189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61723007072326865590949837 23146127652122574596606189)
              ·
                refine ⟨8679797869545965473727321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23146127652122574596606189 8679797869545965473727321)
                ·
                  refine ⟨6509848402159474105295491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8679797869545965473727321 6509848402159474105295491)
                  ·
                    refine ⟨9764772603239211157943237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6509848402159474105295491 9764772603239211157943237)
                    ·
                      refine ⟨1830894863107352092114357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9764772603239211157943237 1830894863107352092114357)
                      ·
                        rfl

theorem cell23_3565655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3, 2, 1, 4].length) (baseStart_3565655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3565655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3565655 prefixEnd_3565655 := by exact prefixLift 3565655
  have htrace : WordTrace (prefixWord ++ tailWord_3565655) baseStart_3565655 baseEnd_3565655 := by
    simpa [prefixWord, tailWord_3565655, baseEnd_3565655] using wordTrace_append hprefix tailTrace_3565655
  have hstable : (prefixWord ++ tailWord_3565655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565655).length < 2 ^ (prefixWord ++ tailWord_3565655).sum := by decide
  have hdescent : baseEnd_3565655 < baseStart_3565655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565775 : List Nat := [1, 1, 2, 1, 1, 3, 4, 1, 3, 2, 4]
def baseStart_3565775 : Nat := 118140960795 + 3565775 * 2 ^ 59
def prefixEnd_3565775 : Nat := 4983230072969 + 3 ^ 40 * 3565775 * 2
def baseEnd_3565775 : Nat := 1830956480785891622613805

theorem tailTrace_3565775 : CollatzResearch.WordTrace tailWord_3565775 prefixEnd_3565775 1830956480785891622613805 := by
  unfold tailWord_3565775
  simp only [CollatzResearch.WordTrace]
  refine ⟨130054498656813635731266779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86702999104542423820844519 130054498656813635731266779)
  ·
    refine ⟨195081747985220453596900169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130054498656813635731266779 195081747985220453596900169)
    ·
      refine ⟨146311310988915340197675127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195081747985220453596900169 146311310988915340197675127)
      ·
        refine ⟨219466966483373010296512691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146311310988915340197675127 219466966483373010296512691)
        ·
          refine ⟨329200449725059515444769037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219466966483373010296512691 329200449725059515444769037)
          ·
            refine ⟨123450168646897318291788389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 329200449725059515444769037 123450168646897318291788389)
            ·
              refine ⟨23146906621293247179710323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123450168646897318291788389 23146906621293247179710323)
              ·
                refine ⟨34720359931939870769565485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23146906621293247179710323 34720359931939870769565485)
                ·
                  refine ⟨13020134974477451538587057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34720359931939870769565485 13020134974477451538587057)
                  ·
                    refine ⟨9765101230858088653940293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13020134974477451538587057 9765101230858088653940293)
                    ·
                      refine ⟨1830956480785891622613805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9765101230858088653940293 1830956480785891622613805)
                      ·
                        rfl

theorem cell23_3565775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3, 2, 4].length) (baseStart_3565775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3565775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3565775 prefixEnd_3565775 := by exact prefixLift 3565775
  have htrace : WordTrace (prefixWord ++ tailWord_3565775) baseStart_3565775 baseEnd_3565775 := by
    simpa [prefixWord, tailWord_3565775, baseEnd_3565775] using wordTrace_append hprefix tailTrace_3565775
  have hstable : (prefixWord ++ tailWord_3565775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565775).length < 2 ^ (prefixWord ++ tailWord_3565775).sum := by decide
  have hdescent : baseEnd_3565775 < baseStart_3565775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565789 : List Nat := [1, 4, 3, 2, 1, 1, 2, 1, 4, 4]
def baseStart_3565789 : Nat := 118140960795 + 3565789 * 2 ^ 59
def prefixEnd_3565789 : Nat := 4983230072969 + 3 ^ 40 * 3565789 * 2
def baseEnd_3565789 : Nat := 610321223171684855946247

theorem tailTrace_3565789 : CollatzResearch.WordTrace tailWord_3565789 prefixEnd_3565789 610321223171684855946247 := by
  unfold tailWord_3565789
  simp only [CollatzResearch.WordTrace]
  refine ⟨130055009278762916122276421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86703339519175277414850947 130055009278762916122276421)
  ·
    refine ⟨24385314239768046772926829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130055009278762916122276421 24385314239768046772926829)
    ·
      refine ⟨9144492839913017539847561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24385314239768046772926829 9144492839913017539847561)
      ·
        refine ⟨6858369629934763154885671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9144492839913017539847561 6858369629934763154885671)
        ·
          refine ⟨10287554444902144732328507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6858369629934763154885671 10287554444902144732328507)
          ·
            refine ⟨15431331667353217098492761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10287554444902144732328507 15431331667353217098492761)
            ·
              refine ⟨11573498750514912823869571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15431331667353217098492761 11573498750514912823869571)
              ·
                refine ⟨17360248125772369235804357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11573498750514912823869571 17360248125772369235804357)
                ·
                  refine ⟨3255046523582319231713317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17360248125772369235804357 3255046523582319231713317)
                  ·
                    refine ⟨610321223171684855946247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3255046523582319231713317 610321223171684855946247)
                    ·
                      rfl

theorem cell23_3565789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_3565789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3565789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3565789 prefixEnd_3565789 := by exact prefixLift 3565789
  have htrace : WordTrace (prefixWord ++ tailWord_3565789) baseStart_3565789 baseEnd_3565789 := by
    simpa [prefixWord, tailWord_3565789, baseEnd_3565789] using wordTrace_append hprefix tailTrace_3565789
  have hstable : (prefixWord ++ tailWord_3565789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565789).length < 2 ^ (prefixWord ++ tailWord_3565789).sum := by decide
  have hdescent : baseEnd_3565789 < baseStart_3565789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565839 : List Nat := [1, 1, 2, 1, 1, 1, 3, 7, 1, 3, 2]
def baseStart_3565839 : Nat := 118140960795 + 3565839 * 2 ^ 59
def prefixEnd_3565839 : Nat := 4983230072969 + 3 ^ 40 * 3565839 * 2
def baseEnd_3565839 : Nat := 1830989343547779372213511

theorem tailTrace_3565839 : CollatzResearch.WordTrace tailWord_3565839 prefixEnd_3565839 1830989343547779372213511 := by
  unfold tailWord_3565839
  simp only [CollatzResearch.WordTrace]
  refine ⟨130056832928581774661596571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86704555285721183107731047 130056832928581774661596571)
  ·
    refine ⟨195085249392872661992394857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130056832928581774661596571 195085249392872661992394857)
    ·
      refine ⟨146313937044654496494296143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195085249392872661992394857 146313937044654496494296143)
      ·
        refine ⟨219470905566981744741444215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146313937044654496494296143 219470905566981744741444215)
        ·
          refine ⟨329206358350472617112166323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219470905566981744741444215 329206358350472617112166323)
          ·
            refine ⟨493809537525708925668249485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329206358350472617112166323 493809537525708925668249485)
            ·
              refine ⟨185178576572140847125593557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 493809537525708925668249485 185178576572140847125593557)
              ·
                refine ⟨4340122888409551104506099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 185178576572140847125593557 4340122888409551104506099)
                ·
                  refine ⟨6510184332614326656759149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4340122888409551104506099 6510184332614326656759149)
                  ·
                    refine ⟨2441319124730372496284681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6510184332614326656759149 2441319124730372496284681)
                    ·
                      refine ⟨1830989343547779372213511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2441319124730372496284681 1830989343547779372213511)
                      ·
                        rfl

theorem cell23_3565839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 7, 1, 3, 2].length) (baseStart_3565839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3565839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3565839 prefixEnd_3565839 := by exact prefixLift 3565839
  have htrace : WordTrace (prefixWord ++ tailWord_3565839) baseStart_3565839 baseEnd_3565839 := by
    simpa [prefixWord, tailWord_3565839, baseEnd_3565839] using wordTrace_append hprefix tailTrace_3565839
  have hstable : (prefixWord ++ tailWord_3565839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565839).length < 2 ^ (prefixWord ++ tailWord_3565839).sum := by decide
  have hdescent : baseEnd_3565839 < baseStart_3565839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565886 : List Nat := [4, 2, 1, 2, 1, 2, 2, 2, 1, 4, 2]
def baseStart_3565886 : Nat := 118140960795 + 3565886 * 2 ^ 59
def prefixEnd_3565886 : Nat := 4983230072969 + 3 ^ 40 * 3565886 * 2
def baseEnd_3565886 : Nat := 1831013477138540688325795

theorem tailTrace_3565886 : CollatzResearch.WordTrace tailWord_3565886 prefixEnd_3565886 1831013477138540688325795 := by
  unfold tailWord_3565886
  simp only [CollatzResearch.WordTrace]
  refine ⟨16257318394926437711069689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86705698106274334459038341 16257318394926437711069689)
  ·
    refine ⟨12192988796194828283302267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16257318394926437711069689 12192988796194828283302267)
    ·
      refine ⟨18289483194292242424953401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12192988796194828283302267 18289483194292242424953401)
      ·
        refine ⟨13717112395719181818715051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18289483194292242424953401 13717112395719181818715051)
        ·
          refine ⟨20575668593578772728072577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13717112395719181818715051 20575668593578772728072577)
          ·
            refine ⟨15431751445184079546054433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20575668593578772728072577 15431751445184079546054433)
            ·
              refine ⟨11573813583888059659540825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15431751445184079546054433 11573813583888059659540825)
              ·
                refine ⟨8680360187916044744655619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11573813583888059659540825 8680360187916044744655619)
                ·
                  refine ⟨13020540281874067116983429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8680360187916044744655619 13020540281874067116983429)
                  ·
                    refine ⟨2441351302851387584434393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13020540281874067116983429 2441351302851387584434393)
                    ·
                      refine ⟨1831013477138540688325795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2441351302851387584434393 1831013477138540688325795)
                      ·
                        rfl

theorem cell23_3565886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_3565886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3565886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3565886 prefixEnd_3565886 := by exact prefixLift 3565886
  have htrace : WordTrace (prefixWord ++ tailWord_3565886) baseStart_3565886 baseEnd_3565886 := by
    simpa [prefixWord, tailWord_3565886, baseEnd_3565886] using wordTrace_append hprefix tailTrace_3565886
  have hstable : (prefixWord ++ tailWord_3565886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565886).length < 2 ^ (prefixWord ++ tailWord_3565886).sum := by decide
  have hdescent : baseEnd_3565886 < baseStart_3565886 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565909 : List Nat := [1, 3, 2, 2, 4, 1, 2, 1, 7]
def baseStart_3565909 : Nat := 118140960795 + 3565909 * 2 ^ 59
def prefixEnd_3565909 : Nat := 4983230072969 + 3 ^ 40 * 3565909 * 2
def baseEnd_3565909 : Nat := 203447254132621566482021

theorem tailTrace_3565909 : CollatzResearch.WordTrace tailWord_3565909 prefixEnd_3565909 203447254132621566482021 := by
  unfold tailWord_3565909
  simp only [CollatzResearch.WordTrace]
  refine ⟨130059386038328176616644781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86706257358885451077763187 130059386038328176616644781)
  ·
    refine ⟨48772269764373066231241793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130059386038328176616644781 48772269764373066231241793)
    ·
      refine ⟨36579202323279799673431345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48772269764373066231241793 36579202323279799673431345)
      ·
        refine ⟨27434401742459849755073509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36579202323279799673431345 27434401742459849755073509)
        ·
          refine ⟨5143950326711221829076283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27434401742459849755073509 5143950326711221829076283)
          ·
            refine ⟨7715925490066832743614425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5143950326711221829076283 7715925490066832743614425)
            ·
              refine ⟨5786944117550124557710819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7715925490066832743614425 5786944117550124557710819)
              ·
                refine ⟨8680416176325186836566229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5786944117550124557710819 8680416176325186836566229)
                ·
                  refine ⟨203447254132621566482021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8680416176325186836566229 203447254132621566482021)
                  ·
                    rfl

theorem cell23_3565909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 1, 7].length) (baseStart_3565909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3565909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3565909 prefixEnd_3565909 := by exact prefixLift 3565909
  have htrace : WordTrace (prefixWord ++ tailWord_3565909) baseStart_3565909 baseEnd_3565909 := by
    simpa [prefixWord, tailWord_3565909, baseEnd_3565909] using wordTrace_append hprefix tailTrace_3565909
  have hstable : (prefixWord ++ tailWord_3565909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565909).length < 2 ^ (prefixWord ++ tailWord_3565909).sum := by decide
  have hdescent : baseEnd_3565909 < baseStart_3565909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565920 : List Nat := [2, 1, 1, 3, 5, 1, 3, 1, 2, 2, 2]
def baseStart_3565920 : Nat := 118140960795 + 3565920 * 2 ^ 59
def prefixEnd_3565920 : Nat := 4983230072969 + 3 ^ 40 * 3565920 * 2
def baseEnd_3565920 : Nat := 1831030935480793555300639

theorem tailTrace_3565920 : CollatzResearch.WordTrace tailWord_3565920 prefixEnd_3565920 1831030935480793555300639 := by
  unfold tailWord_3565920
  simp only [CollatzResearch.WordTrace]
  refine ⟨65029893620644162747647607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86706524827525550330196809 65029893620644162747647607)
  ·
    refine ⟨97544840430966244121471411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65029893620644162747647607 97544840430966244121471411)
    ·
      refine ⟨146317260646449366182207117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97544840430966244121471411 146317260646449366182207117)
      ·
        refine ⟨54868972742418512318327669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146317260646449366182207117 54868972742418512318327669)
        ·
          refine ⟨5143966194601735529843219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54868972742418512318327669 5143966194601735529843219)
          ·
            refine ⟨7715949291902603294764829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5143966194601735529843219 7715949291902603294764829)
            ·
              refine ⟨2893480984463476235536811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7715949291902603294764829 2893480984463476235536811)
              ·
                refine ⟨4340221476695214353305217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2893480984463476235536811 4340221476695214353305217)
                ·
                  refine ⟨3255166107521410764978913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4340221476695214353305217 3255166107521410764978913)
                  ·
                    refine ⟨2441374580641058073734185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3255166107521410764978913 2441374580641058073734185)
                    ·
                      refine ⟨1831030935480793555300639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2441374580641058073734185 1831030935480793555300639)
                      ·
                        rfl

theorem cell23_3565920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 1, 2, 2, 2].length) (baseStart_3565920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3565920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3565920 prefixEnd_3565920 := by exact prefixLift 3565920
  have htrace : WordTrace (prefixWord ++ tailWord_3565920) baseStart_3565920 baseEnd_3565920 := by
    simpa [prefixWord, tailWord_3565920, baseEnd_3565920] using wordTrace_append hprefix tailTrace_3565920
  have hstable : (prefixWord ++ tailWord_3565920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565920).length < 2 ^ (prefixWord ++ tailWord_3565920).sum := by decide
  have hdescent : baseEnd_3565920 < baseStart_3565920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3565959 : List Nat := [1, 1, 4, 2, 2, 1, 3, 2, 2, 1, 4]
def baseStart_3565959 : Nat := 118140960795 + 3565959 * 2 ^ 59
def prefixEnd_3565959 : Nat := 4983230072969 + 3 ^ 40 * 3565959 * 2
def baseEnd_3565959 : Nat := 1831050961226318902712959

theorem tailTrace_3565959 : CollatzResearch.WordTrace tailWord_3565959 prefixEnd_3565959 1831050961226318902712959 := by
  unfold tailWord_3565959
  simp only [CollatzResearch.WordTrace]
  refine ⟨130061209688147035155964931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86707473125431356770643287 130061209688147035155964931)
  ·
    refine ⟨195091814532220552733947397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130061209688147035155964931 195091814532220552733947397)
    ·
      refine ⟨36579715224791353637615137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195091814532220552733947397 36579715224791353637615137)
      ·
        refine ⟨27434786418593515228211353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36579715224791353637615137 27434786418593515228211353)
        ·
          refine ⟨20576089813945136421158515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27434786418593515228211353 20576089813945136421158515)
          ·
            refine ⟨30864134720917704631737773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20576089813945136421158515 30864134720917704631737773)
            ·
              refine ⟨11574050520344139236901665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30864134720917704631737773 11574050520344139236901665)
              ·
                refine ⟨8680537890258104427676249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11574050520344139236901665 8680537890258104427676249)
                ·
                  refine ⟨6510403417693578320757187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8680537890258104427676249 6510403417693578320757187)
                  ·
                    refine ⟨9765605126540367481135781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6510403417693578320757187 9765605126540367481135781)
                    ·
                      refine ⟨1831050961226318902712959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9765605126540367481135781 1831050961226318902712959)
                      ·
                        rfl

theorem cell23_3565959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_3565959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3565959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3565959 prefixEnd_3565959 := by exact prefixLift 3565959
  have htrace : WordTrace (prefixWord ++ tailWord_3565959) baseStart_3565959 baseEnd_3565959 := by
    simpa [prefixWord, tailWord_3565959, baseEnd_3565959] using wordTrace_append hprefix tailTrace_3565959
  have hstable : (prefixWord ++ tailWord_3565959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3565959).length < 2 ^ (prefixWord ++ tailWord_3565959).sum := by decide
  have hdescent : baseEnd_3565959 < baseStart_3565959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3565959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566019 : List Nat := [1, 1, 1, 3, 1, 1, 3, 2, 3, 5, 2]
def baseStart_3566019 : Nat := 118140960795 + 3566019 * 2 ^ 59
def prefixEnd_3566019 : Nat := 4983230072969 + 3 ^ 40 * 3566019 * 2
def baseEnd_3566019 : Nat := 1831081770065588667962683

theorem tailTrace_3566019 : CollatzResearch.WordTrace tailWord_3566019 prefixEnd_3566019 1831081770065588667962683 := by
  unfold tailWord_3566019
  simp only [CollatzResearch.WordTrace]
  refine ⟨130063398067929665403149111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86708932045286443602099407 130063398067929665403149111)
  ·
    refine ⟨195095097101894498104723667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130063398067929665403149111 195095097101894498104723667)
    ·
      refine ⟨292642645652841747157085501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195095097101894498104723667 292642645652841747157085501)
      ·
        refine ⟨109740992119815655183907063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 292642645652841747157085501 109740992119815655183907063)
        ·
          refine ⟨164611488179723482775860595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109740992119815655183907063 164611488179723482775860595)
          ·
            refine ⟨246917232269585224163790893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164611488179723482775860595 246917232269585224163790893)
            ·
              refine ⟨92593962101094459061421585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 246917232269585224163790893 92593962101094459061421585)
              ·
                refine ⟨69445471575820844296066189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92593962101094459061421585 69445471575820844296066189)
                ·
                  refine ⟨26042051840932816611024821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69445471575820844296066189 26042051840932816611024821)
                  ·
                    refine ⟨2441442360087451557283577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26042051840932816611024821 2441442360087451557283577)
                    ·
                      refine ⟨1831081770065588667962683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2441442360087451557283577 1831081770065588667962683)
                      ·
                        rfl

theorem cell23_3566019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 5, 2].length) (baseStart_3566019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3566019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3566019 prefixEnd_3566019 := by exact prefixLift 3566019
  have htrace : WordTrace (prefixWord ++ tailWord_3566019) baseStart_3566019 baseEnd_3566019 := by
    simpa [prefixWord, tailWord_3566019, baseEnd_3566019] using wordTrace_append hprefix tailTrace_3566019
  have hstable : (prefixWord ++ tailWord_3566019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566019).length < 2 ^ (prefixWord ++ tailWord_3566019).sum := by decide
  have hdescent : baseEnd_3566019 < baseStart_3566019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566020 : List Nat := [2, 3, 3, 2, 2, 1, 1, 4, 1, 4]
def baseStart_3566020 : Nat := 118140960795 + 3566020 * 2 ^ 59
def prefixEnd_3566020 : Nat := 4983230072969 + 3 ^ 40 * 3566020 * 2
def baseEnd_3566020 : Nat := 610360761182081054683393

theorem tailTrace_3566020 : CollatzResearch.WordTrace tailWord_3566020 prefixEnd_3566020 610360761182081054683393 := by
  unfold tailWord_3566020
  simp only [CollatzResearch.WordTrace]
  refine ⟨65031717270463021286967757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86708956360617361715957009 65031717270463021286967757)
  ·
    refine ⟨24386893976423632982612909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65031717270463021286967757 24386893976423632982612909)
    ·
      refine ⟨9145085241158862368479841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24386893976423632982612909 9145085241158862368479841)
      ·
        refine ⟨6858813930869146776359881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9145085241158862368479841 6858813930869146776359881)
        ·
          refine ⟨5144110448151860082269911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6858813930869146776359881 5144110448151860082269911)
          ·
            refine ⟨7716165672227790123404867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5144110448151860082269911 7716165672227790123404867)
            ·
              refine ⟨11574248508341685185107301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7716165672227790123404867 11574248508341685185107301)
              ·
                refine ⟨2170171595314065972207619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11574248508341685185107301 2170171595314065972207619)
                ·
                  refine ⟨3255257392971098958311429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2170171595314065972207619 3255257392971098958311429)
                  ·
                    refine ⟨610360761182081054683393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3255257392971098958311429 610360761182081054683393)
                    ·
                      rfl

theorem cell23_3566020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_3566020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3566020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3566020 prefixEnd_3566020 := by exact prefixLift 3566020
  have htrace : WordTrace (prefixWord ++ tailWord_3566020) baseStart_3566020 baseEnd_3566020 := by
    simpa [prefixWord, tailWord_3566020, baseEnd_3566020] using wordTrace_append hprefix tailTrace_3566020
  have hstable : (prefixWord ++ tailWord_3566020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566020).length < 2 ^ (prefixWord ++ tailWord_3566020).sum := by decide
  have hdescent : baseEnd_3566020 < baseStart_3566020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566026 : List Nat := [3, 1, 2, 1, 2, 2, 2, 3, 3, 1, 3]
def baseStart_3566026 : Nat := 118140960795 + 3566026 * 2 ^ 59
def prefixEnd_3566026 : Nat := 4983230072969 + 3 ^ 40 * 3566026 * 2
def baseEnd_3566026 : Nat := 1831085364430170140575151

theorem tailTrace_3566026 : CollatzResearch.WordTrace tailWord_3566026 prefixEnd_3566026 1831085364430170140575151 := by
  unfold tailWord_3566026
  simp only [CollatzResearch.WordTrace]
  refine ⟨32515913344726076399663483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86709102252602870399102621 32515913344726076399663483)
  ·
    refine ⟨48773870017089114599495225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32515913344726076399663483 48773870017089114599495225)
    ·
      refine ⟨36580402512816835949621419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48773870017089114599495225 36580402512816835949621419)
      ·
        refine ⟨54870603769225253924432129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36580402512816835949621419 54870603769225253924432129)
        ·
          refine ⟨41152952826918940443324097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54870603769225253924432129 41152952826918940443324097)
          ·
            refine ⟨30864714620189205332493073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41152952826918940443324097 30864714620189205332493073)
            ·
              refine ⟨23148535965141903999369805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30864714620189205332493073 23148535965141903999369805)
              ·
                refine ⟨8680700986928213999763677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23148535965141903999369805 8680700986928213999763677)
                ·
                  refine ⟨3255262870098080249911379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8680700986928213999763677 3255262870098080249911379)
                  ·
                    refine ⟨4882894305147120374867069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3255262870098080249911379 4882894305147120374867069)
                    ·
                      refine ⟨1831085364430170140575151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4882894305147120374867069 1831085364430170140575151)
                      ·
                        rfl

theorem cell23_3566026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3, 3, 1, 3].length) (baseStart_3566026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3566026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3566026 prefixEnd_3566026 := by exact prefixLift 3566026
  have htrace : WordTrace (prefixWord ++ tailWord_3566026) baseStart_3566026 baseEnd_3566026 := by
    simpa [prefixWord, tailWord_3566026, baseEnd_3566026] using wordTrace_append hprefix tailTrace_3566026
  have hstable : (prefixWord ++ tailWord_3566026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566026).length < 2 ^ (prefixWord ++ tailWord_3566026).sum := by decide
  have hdescent : baseEnd_3566026 < baseStart_3566026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566032 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 4]
def baseStart_3566032 : Nat := 118140960795 + 3566032 * 2 ^ 59
def prefixEnd_3566032 : Nat := 4983230072969 + 3 ^ 40 * 3566032 * 2
def baseEnd_3566032 : Nat := 1831088445314097117100123

theorem tailTrace_3566032 : CollatzResearch.WordTrace tailWord_3566032 prefixEnd_3566032 1831088445314097117100123 := by
  unfold tailWord_3566032
  simp only [CollatzResearch.WordTrace]
  refine ⟨65031936108441284311686175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86709248144588379082248233 65031936108441284311686175)
  ·
    refine ⟨97547904162661926467529263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65031936108441284311686175 97547904162661926467529263)
    ·
      refine ⟨146321856243992889701293895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97547904162661926467529263 146321856243992889701293895)
      ·
        refine ⟨219482784365989334551940843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146321856243992889701293895 219482784365989334551940843)
        ·
          refine ⟨329224176548984001827911265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219482784365989334551940843 329224176548984001827911265)
          ·
            refine ⟨246918132411738001370933449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 329224176548984001827911265 246918132411738001370933449)
            ·
              refine ⟨185188599308803501028200087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246918132411738001370933449 185188599308803501028200087)
              ·
                refine ⟨277782898963205251542300131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185188599308803501028200087 277782898963205251542300131)
                ·
                  refine ⟨416674348444807877313450197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 277782898963205251542300131 416674348444807877313450197)
                  ·
                    refine ⟨9765805041675184624533989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 416674348444807877313450197 9765805041675184624533989)
                    ·
                      refine ⟨1831088445314097117100123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9765805041675184624533989 1831088445314097117100123)
                      ·
                        rfl

theorem cell23_3566032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 4].length) (baseStart_3566032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3566032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3566032 prefixEnd_3566032 := by exact prefixLift 3566032
  have htrace : WordTrace (prefixWord ++ tailWord_3566032) baseStart_3566032 baseEnd_3566032 := by
    simpa [prefixWord, tailWord_3566032, baseEnd_3566032] using wordTrace_append hprefix tailTrace_3566032
  have hstable : (prefixWord ++ tailWord_3566032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566032).length < 2 ^ (prefixWord ++ tailWord_3566032).sum := by decide
  have hdescent : baseEnd_3566032 < baseStart_3566032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566049 : List Nat := [1, 2, 3, 1, 2, 2, 1, 3, 3, 1, 4]
def baseStart_3566049 : Nat := 118140960795 + 3566049 * 2 ^ 59
def prefixEnd_3566049 : Nat := 4983230072969 + 3 ^ 40 * 3566049 * 2
def baseEnd_3566049 : Nat := 1831097174485223550587545

theorem tailTrace_3566049 : CollatzResearch.WordTrace tailWord_3566049 prefixEnd_3566049 1831097174485223550587545 := by
  unfold tailWord_3566049
  simp only [CollatzResearch.WordTrace]
  refine ⟨130064492257820980526741201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86709661505213987017827467 130064492257820980526741201)
  ·
    refine ⟨97548369193365735395055901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130064492257820980526741201 97548369193365735395055901)
    ·
      refine ⟨36580638447512150773145963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97548369193365735395055901 36580638447512150773145963)
      ·
        refine ⟨54870957671268226159718945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36580638447512150773145963 54870957671268226159718945)
        ·
          refine ⟨41153218253451169619789209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54870957671268226159718945 41153218253451169619789209)
          ·
            refine ⟨30864913690088377214841907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41153218253451169619789209 30864913690088377214841907)
            ·
              refine ⟨46297370535132565822262861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30864913690088377214841907 46297370535132565822262861)
              ·
                refine ⟨17361513950674712183348573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46297370535132565822262861 17361513950674712183348573)
                ·
                  refine ⟨6510567731503017068755715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17361513950674712183348573 6510567731503017068755715)
                  ·
                    refine ⟨9765851597254525603133573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6510567731503017068755715 9765851597254525603133573)
                    ·
                      refine ⟨1831097174485223550587545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9765851597254525603133573 1831097174485223550587545)
                      ·
                        rfl

theorem cell23_3566049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 3, 1, 4].length) (baseStart_3566049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3566049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3566049 prefixEnd_3566049 := by exact prefixLift 3566049
  have htrace : WordTrace (prefixWord ++ tailWord_3566049) baseStart_3566049 baseEnd_3566049 := by
    simpa [prefixWord, tailWord_3566049, baseEnd_3566049] using wordTrace_append hprefix tailTrace_3566049
  have hstable : (prefixWord ++ tailWord_3566049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566049).length < 2 ^ (prefixWord ++ tailWord_3566049).sum := by decide
  have hdescent : baseEnd_3566049 < baseStart_3566049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566053 : List Nat := [1, 3, 1, 5, 2, 1, 1, 1, 1, 5, 2]
def baseStart_3566053 : Nat := 118140960795 + 3566053 * 2 ^ 59
def prefixEnd_3566053 : Nat := 4983230072969 + 3 ^ 40 * 3566053 * 2
def baseEnd_3566053 : Nat := 1831099228407841534937527

theorem tailTrace_3566053 : CollatzResearch.WordTrace tailWord_3566053 prefixEnd_3566053 1831099228407841534937527 := by
  unfold tailWord_3566053
  simp only [CollatzResearch.WordTrace]
  refine ⟨130064638149806489209886813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86709758766537659473257875 130064638149806489209886813)
  ·
    refine ⟨48774239306177433453707555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130064638149806489209886813 48774239306177433453707555)
    ·
      refine ⟨73161358959266150180561333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48774239306177433453707555 73161358959266150180561333)
      ·
        refine ⟨6858877402431201579427625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73161358959266150180561333 6858877402431201579427625)
        ·
          refine ⟨5144158051823401184570719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6858877402431201579427625 5144158051823401184570719)
          ·
            refine ⟨7716237077735101776856079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5144158051823401184570719 7716237077735101776856079)
            ·
              refine ⟨11574355616602652665284119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7716237077735101776856079 11574355616602652665284119)
              ·
                refine ⟨17361533424903978997926179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11574355616602652665284119 17361533424903978997926179)
                ·
                  refine ⟨26042300137355968496889269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17361533424903978997926179 26042300137355968496889269)
                  ·
                    refine ⟨2441465637877122046583369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26042300137355968496889269 2441465637877122046583369)
                    ·
                      refine ⟨1831099228407841534937527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2441465637877122046583369 1831099228407841534937527)
                      ·
                        rfl

theorem cell23_3566053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_3566053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3566053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3566053 prefixEnd_3566053 := by exact prefixLift 3566053
  have htrace : WordTrace (prefixWord ++ tailWord_3566053) baseStart_3566053 baseEnd_3566053 := by
    simpa [prefixWord, tailWord_3566053, baseEnd_3566053] using wordTrace_append hprefix tailTrace_3566053
  have hstable : (prefixWord ++ tailWord_3566053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566053).length < 2 ^ (prefixWord ++ tailWord_3566053).sum := by decide
  have hdescent : baseEnd_3566053 < baseStart_3566053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566059 : List Nat := [1, 1, 1, 1, 2, 3, 4, 2, 4, 4]
def baseStart_3566059 : Nat := 118140960795 + 3566059 * 2 ^ 59
def prefixEnd_3566059 : Nat := 4983230072969 + 3 ^ 40 * 3566059 * 2
def baseEnd_3566059 : Nat := 610367436430589503820833

theorem tailTrace_3566059 : CollatzResearch.WordTrace tailWord_3566059 prefixEnd_3566059 610367436430589503820833 := by
  unfold tailWord_3566059
  simp only [CollatzResearch.WordTrace]
  refine ⟨130064856987784752234605231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86709904658523168156403487 130064856987784752234605231)
  ·
    refine ⟨195097285481677128351907847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130064856987784752234605231 195097285481677128351907847)
    ·
      refine ⟨292645928222515692527861771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195097285481677128351907847 292645928222515692527861771)
      ·
        refine ⟨438968892333773538791792657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292645928222515692527861771 438968892333773538791792657)
        ·
          refine ⟨329226669250330154093844493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 438968892333773538791792657 329226669250330154093844493)
          ·
            refine ⟨123460000968873807785191685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 329226669250330154093844493 123460000968873807785191685)
            ·
              refine ⟨23148750181663838959723441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123460000968873807785191685 23148750181663838959723441)
              ·
                refine ⟨17361562636247879219792581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23148750181663838959723441 17361562636247879219792581)
                ·
                  refine ⟨3255292994296477353711109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17361562636247879219792581 3255292994296477353711109)
                  ·
                    refine ⟨610367436430589503820833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3255292994296477353711109 610367436430589503820833)
                    ·
                      rfl

theorem cell23_3566059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 4, 4].length) (baseStart_3566059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3566059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3566059 prefixEnd_3566059 := by exact prefixLift 3566059
  have htrace : WordTrace (prefixWord ++ tailWord_3566059) baseStart_3566059 baseEnd_3566059 := by
    simpa [prefixWord, tailWord_3566059, baseEnd_3566059] using wordTrace_append hprefix tailTrace_3566059
  have hstable : (prefixWord ++ tailWord_3566059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566059).length < 2 ^ (prefixWord ++ tailWord_3566059).sum := by decide
  have hdescent : baseEnd_3566059 < baseStart_3566059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566072 : List Nat := [2, 1, 2, 1, 1, 4, 12]
def baseStart_3566072 : Nat := 118140960795 + 3566072 * 2 ^ 59
def prefixEnd_3566072 : Nat := 4983230072969 + 3 ^ 40 * 3566072 * 2
def baseEnd_3566072 : Nat := 22606283759756505686419

theorem tailTrace_3566072 : CollatzResearch.WordTrace tailWord_3566072 prefixEnd_3566072 22606283759756505686419 := by
  unfold tailWord_3566072
  simp only [CollatzResearch.WordTrace]
  refine ⟨65032665568368827727414235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86710220757825103636552313 65032665568368827727414235)
  ·
    refine ⟨97548998352553241591121353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65032665568368827727414235 97548998352553241591121353)
    ·
      refine ⟨73161748764414931193341015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97548998352553241591121353 73161748764414931193341015)
      ·
        refine ⟨109742623146622396790011523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73161748764414931193341015 109742623146622396790011523)
        ·
          refine ⟨164613934719933595185017285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109742623146622396790011523 164613934719933595185017285)
          ·
            refine ⟨30865112759987549097190741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 164613934719933595185017285 30865112759987549097190741)
            ·
              refine ⟨22606283759756505686419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 30865112759987549097190741 22606283759756505686419)
              ·
                rfl

theorem cell23_3566072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 12].length) (baseStart_3566072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3566072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3566072 prefixEnd_3566072 := by exact prefixLift 3566072
  have htrace : WordTrace (prefixWord ++ tailWord_3566072) baseStart_3566072 baseEnd_3566072 := by
    simpa [prefixWord, tailWord_3566072, baseEnd_3566072] using wordTrace_append hprefix tailTrace_3566072
  have hstable : (prefixWord ++ tailWord_3566072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566072).length < 2 ^ (prefixWord ++ tailWord_3566072).sum := by decide
  have hdescent : baseEnd_3566072 < baseStart_3566072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566083 : List Nat := [1, 1, 1, 3, 2, 1, 6, 1, 3, 2, 2]
def baseStart_3566083 : Nat := 118140960795 + 3566083 * 2 ^ 59
def prefixEnd_3566083 : Nat := 4983230072969 + 3 ^ 40 * 3566083 * 2
def baseEnd_3566083 : Nat := 1831114632827476417562389

theorem tailTrace_3566083 : CollatzResearch.WordTrace tailWord_3566083 prefixEnd_3566083 1831114632827476417562389 := by
  unfold tailWord_3566083
  simp only [CollatzResearch.WordTrace]
  refine ⟨130065732339697804333478903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86710488226465202888985935 130065732339697804333478903)
  ·
    refine ⟨195098598509546706500218355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130065732339697804333478903 195098598509546706500218355)
    ·
      refine ⟨292647897764320059750327533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195098598509546706500218355 292647897764320059750327533)
      ·
        refine ⟨109742961661620022406372825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 292647897764320059750327533 109742961661620022406372825)
        ·
          refine ⟨82307221246215016804779619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109742961661620022406372825 82307221246215016804779619)
          ·
            refine ⟨123460831869322525207169429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82307221246215016804779619 123460831869322525207169429)
            ·
              refine ⟨5787226493874493369086067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 123460831869322525207169429 5787226493874493369086067)
              ·
                refine ⟨8680839740811740053629101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5787226493874493369086067 8680839740811740053629101)
                ·
                  refine ⟨3255314902804402520110913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8680839740811740053629101 3255314902804402520110913)
                  ·
                    refine ⟨2441486177103301890083185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3255314902804402520110913 2441486177103301890083185)
                    ·
                      refine ⟨1831114632827476417562389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2441486177103301890083185 1831114632827476417562389)
                      ·
                        rfl

theorem cell23_3566083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 1, 3, 2, 2].length) (baseStart_3566083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3566083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3566083 prefixEnd_3566083 := by exact prefixLift 3566083
  have htrace : WordTrace (prefixWord ++ tailWord_3566083) baseStart_3566083 baseEnd_3566083 := by
    simpa [prefixWord, tailWord_3566083, baseEnd_3566083] using wordTrace_append hprefix tailTrace_3566083
  have hstable : (prefixWord ++ tailWord_3566083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566083).length < 2 ^ (prefixWord ++ tailWord_3566083).sum := by decide
  have hdescent : baseEnd_3566083 < baseStart_3566083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566100 : List Nat := [2, 4, 3, 1, 1, 2, 2, 2, 1, 1, 4]
def baseStart_3566100 : Nat := 118140960795 + 3566100 * 2 ^ 59
def prefixEnd_3566100 : Nat := 4983230072969 + 3 ^ 40 * 3566100 * 2
def baseEnd_3566100 : Nat := 1831123361998602851049811

theorem tailTrace_3566100 : CollatzResearch.WordTrace tailWord_3566100 prefixEnd_3566100 1831123361998602851049811 := by
  unfold tailWord_3566100
  simp only [CollatzResearch.WordTrace]
  refine ⟨65033176190318108118423877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86710901587090810824565169 65033176190318108118423877)
  ·
    refine ⟨12193720535684645272204477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65033176190318108118423877 12193720535684645272204477)
    ·
      refine ⟨4572645200881741977076679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12193720535684645272204477 4572645200881741977076679)
      ·
        refine ⟨6858967801322612965615019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4572645200881741977076679 6858967801322612965615019)
        ·
          refine ⟨10288451701983919448422529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6858967801322612965615019 10288451701983919448422529)
          ·
            refine ⟨7716338776487939586316897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10288451701983919448422529 7716338776487939586316897)
            ·
              refine ⟨5787254082365954689737673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7716338776487939586316897 5787254082365954689737673)
              ·
                refine ⟨4340440561774466017303255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5787254082365954689737673 4340440561774466017303255)
                ·
                  refine ⟨6510660842661699025954883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4340440561774466017303255 6510660842661699025954883)
                  ·
                    refine ⟨9765991263992548538932325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6510660842661699025954883 9765991263992548538932325)
                    ·
                      refine ⟨1831123361998602851049811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9765991263992548538932325 1831123361998602851049811)
                      ·
                        rfl

theorem cell23_3566100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_3566100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3566100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3566100 prefixEnd_3566100 := by exact prefixLift 3566100
  have htrace : WordTrace (prefixWord ++ tailWord_3566100) baseStart_3566100 baseEnd_3566100 := by
    simpa [prefixWord, tailWord_3566100, baseEnd_3566100] using wordTrace_append hprefix tailTrace_3566100
  have hstable : (prefixWord ++ tailWord_3566100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566100).length < 2 ^ (prefixWord ++ tailWord_3566100).sum := by decide
  have hdescent : baseEnd_3566100 < baseStart_3566100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3566133 : List Nat := [1, 3, 3, 1, 1, 2, 2, 4, 2, 1, 3]
def baseStart_3566133 : Nat := 118140960795 + 3566133 * 2 ^ 59
def prefixEnd_3566133 : Nat := 4983230072969 + 3 ^ 40 * 3566133 * 2
def baseEnd_3566133 : Nat := 1831140306860201221937159

theorem tailTrace_3566133 : CollatzResearch.WordTrace tailWord_3566133 prefixEnd_3566133 1831140306860201221937159 := by
  unfold tailWord_3566133
  simp only [CollatzResearch.WordTrace]
  refine ⟨130067555989516662872799053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86711703993011108581866035 130067555989516662872799053)
  ·
    refine ⟨48775333496068748577299645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130067555989516662872799053 48775333496068748577299645)
    ·
      refine ⟨18290750061025780716487367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48775333496068748577299645 18290750061025780716487367)
      ·
        refine ⟨27436125091538671074731051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18290750061025780716487367 27436125091538671074731051)
        ·
          refine ⟨41154187637308006612096577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27436125091538671074731051 41154187637308006612096577)
          ·
            refine ⟨30865640727981004959072433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41154187637308006612096577 30865640727981004959072433)
            ·
              refine ⟨23149230545985753719304325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30865640727981004959072433 23149230545985753719304325)
              ·
                refine ⟨4340480727372328822369561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23149230545985753719304325 4340480727372328822369561)
                ·
                  refine ⟨3255360545529246616777171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4340480727372328822369561 3255360545529246616777171)
                  ·
                    refine ⟨4883040818293869925165757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3255360545529246616777171 4883040818293869925165757)
                    ·
                      refine ⟨1831140306860201221937159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4883040818293869925165757 1831140306860201221937159)
                      ·
                        rfl

theorem cell23_3566133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 4, 2, 1, 3].length) (baseStart_3566133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3566133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3566133 prefixEnd_3566133 := by exact prefixLift 3566133
  have htrace : WordTrace (prefixWord ++ tailWord_3566133) baseStart_3566133 baseEnd_3566133 := by
    simpa [prefixWord, tailWord_3566133, baseEnd_3566133] using wordTrace_append hprefix tailTrace_3566133
  have hstable : (prefixWord ++ tailWord_3566133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3566133).length < 2 ^ (prefixWord ++ tailWord_3566133).sum := by decide
  have hdescent : baseEnd_3566133 < baseStart_3566133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3566133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
