import V185TrunkScan22Chunk197

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1766112 : List Nat := [2, 1, 1, 3, 1, 2, 1, 4, 3, 4]
def baseStart_1766112 : Nat := 118140960795 + 1766112 * 2 ^ 59
def prefixEnd_1766112 : Nat := 4983230072969 + 3 ^ 40 * 1766112 * 2
def baseEnd_1766112 : Nat := 604576230448999541585203

theorem tailTrace_1766112 : CollatzResearch.WordTrace tailWord_1766112 prefixEnd_1766112 604576230448999541585203 := by
  unfold tailWord_1766112
  simp only [CollatzResearch.WordTrace]
  refine ⟨32207698288842663380442295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42943597718456884507256393 32207698288842663380442295)
  ·
    refine ⟨48311547433263995070663443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32207698288842663380442295 48311547433263995070663443)
    ·
      refine ⟨72467321149895992605995165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48311547433263995070663443 72467321149895992605995165)
      ·
        refine ⟨27175245431210997227248187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72467321149895992605995165 27175245431210997227248187)
        ·
          refine ⟨40762868146816495840872281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27175245431210997227248187 40762868146816495840872281)
          ·
            refine ⟨30572151110112371880654211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40762868146816495840872281 30572151110112371880654211)
            ·
              refine ⟨45858226665168557820981317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30572151110112371880654211 45858226665168557820981317)
              ·
                refine ⟨8598417499719104591433997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45858226665168557820981317 8598417499719104591433997)
                ·
                  refine ⟨3224406562394664221787749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8598417499719104591433997 3224406562394664221787749)
                  ·
                    refine ⟨604576230448999541585203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3224406562394664221787749 604576230448999541585203)
                    ·
                      rfl

theorem cell22_1766112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 3, 4].length) (baseStart_1766112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1766112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1766112 prefixEnd_1766112 := by exact prefixLift 1766112
  have htrace : WordTrace (prefixWord ++ tailWord_1766112) baseStart_1766112 baseEnd_1766112 := by
    simpa [prefixWord, tailWord_1766112, baseEnd_1766112] using wordTrace_append hprefix tailTrace_1766112
  have hstable : (prefixWord ++ tailWord_1766112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766112).length < 2 ^ (prefixWord ++ tailWord_1766112).sum := by decide
  have hdescent : baseEnd_1766112 < baseStart_1766112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766116 : List Nat := [2, 3, 1, 1, 1, 6, 2, 1, 5]
def baseStart_1766116 : Nat := 118140960795 + 1766116 * 2 ^ 59
def prefixEnd_1766116 : Nat := 4983230072969 + 3 ^ 40 * 1766116 * 2
def baseEnd_1766116 : Nat := 201525866576914954828397

theorem tailTrace_1766116 : CollatzResearch.WordTrace tailWord_1766116 prefixEnd_1766116 201525866576914954828397 := by
  unfold tailWord_1766116
  simp only [CollatzResearch.WordTrace]
  refine ⟨32207771234835417722015101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42943694979780556962686801 32207771234835417722015101)
  ·
    refine ⟨12077914213063281645755663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32207771234835417722015101 12077914213063281645755663)
    ·
      refine ⟨18116871319594922468633495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12077914213063281645755663 18116871319594922468633495)
      ·
        refine ⟨27175306979392383702950243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18116871319594922468633495 27175306979392383702950243)
        ·
          refine ⟨40762960469088575554425365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27175306979392383702950243 40762960469088575554425365)
          ·
            refine ⟨1910763771988526979113689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 40762960469088575554425365 1910763771988526979113689)
            ·
              refine ⟨1433072828991395234335267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1910763771988526979113689 1433072828991395234335267)
              ·
                refine ⟨2149609243487092851502901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1433072828991395234335267 2149609243487092851502901)
                ·
                  refine ⟨201525866576914954828397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2149609243487092851502901 201525866576914954828397)
                  ·
                    rfl

theorem cell22_1766116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 1, 5].length) (baseStart_1766116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1766116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1766116 prefixEnd_1766116 := by exact prefixLift 1766116
  have htrace : WordTrace (prefixWord ++ tailWord_1766116) baseStart_1766116 baseEnd_1766116 := by
    simpa [prefixWord, tailWord_1766116, baseEnd_1766116] using wordTrace_append hprefix tailTrace_1766116
  have hstable : (prefixWord ++ tailWord_1766116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766116).length < 2 ^ (prefixWord ++ tailWord_1766116).sum := by decide
  have hdescent : baseEnd_1766116 < baseStart_1766116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766161 : List Nat := [1, 2, 2, 1, 1, 3, 6, 2, 4]
def baseStart_1766161 : Nat := 118140960795 + 1766161 * 2 ^ 59
def prefixEnd_1766161 : Nat := 4983230072969 + 3 ^ 40 * 1766161 * 2
def baseEnd_1766161 : Nat := 201531001383459915703351

theorem tailTrace_1766161 : CollatzResearch.WordTrace tailWord_1766161 prefixEnd_1766161 201531001383459915703351 := by
  unfold tailWord_1766161
  simp only [CollatzResearch.WordTrace]
  refine ⟨64417183754507808129418337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42944789169671872086278891 64417183754507808129418337)
  ·
    refine ⟨48312887815880856097063753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64417183754507808129418337 48312887815880856097063753)
    ·
      refine ⟨36234665861910642072797815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48312887815880856097063753 36234665861910642072797815)
      ·
        refine ⟨54351998792865963109196723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36234665861910642072797815 54351998792865963109196723)
        ·
          refine ⟨81527998189298944663795085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54351998792865963109196723 81527998189298944663795085)
          ·
            refine ⟨30572999320987104248923157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81527998189298944663795085 30572999320987104248923157)
            ·
              refine ⟨1433109343171270511668273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30572999320987104248923157 1433109343171270511668273)
              ·
                refine ⟨1074832007378452883751205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1433109343171270511668273 1074832007378452883751205)
                ·
                  refine ⟨201531001383459915703351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1074832007378452883751205 201531001383459915703351)
                  ·
                    rfl

theorem cell22_1766161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 2, 4].length) (baseStart_1766161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1766161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1766161 prefixEnd_1766161 := by exact prefixLift 1766161
  have htrace : WordTrace (prefixWord ++ tailWord_1766161) baseStart_1766161 baseEnd_1766161 := by
    simpa [prefixWord, tailWord_1766161, baseEnd_1766161] using wordTrace_append hprefix tailTrace_1766161
  have hstable : (prefixWord ++ tailWord_1766161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766161).length < 2 ^ (prefixWord ++ tailWord_1766161).sum := by decide
  have hdescent : baseEnd_1766161 < baseStart_1766161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766176 : List Nat := [2, 1, 1, 5, 1, 2, 2, 3, 2, 3]
def baseStart_1766176 : Nat := 118140960795 + 1766176 * 2 ^ 59
def prefixEnd_1766176 : Nat := 4983230072969 + 3 ^ 40 * 1766176 * 2
def baseEnd_1766176 : Nat := 604598138956924707985007

theorem tailTrace_1766176 : CollatzResearch.WordTrace tailWord_1766176 prefixEnd_1766176 604598138956924707985007 := by
  unfold tailWord_1766176
  simp only [CollatzResearch.WordTrace]
  refine ⟨32208865424726732845607191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42945153899635643794142921 32208865424726732845607191)
  ·
    refine ⟨48313298137090099268410787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32208865424726732845607191 48313298137090099268410787)
    ·
      refine ⟨72469947205635148902616181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48313298137090099268410787 72469947205635148902616181)
      ·
        refine ⟨6794057550528295209620267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72469947205635148902616181 6794057550528295209620267)
        ·
          refine ⟨10191086325792442814430401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6794057550528295209620267 10191086325792442814430401)
          ·
            refine ⟨7643314744344332110822801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10191086325792442814430401 7643314744344332110822801)
            ·
              refine ⟨5732486058258249083117101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7643314744344332110822801 5732486058258249083117101)
              ·
                refine ⟨2149682271846843406168913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5732486058258249083117101 2149682271846843406168913)
                ·
                  refine ⟨1612261703885132554626685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2149682271846843406168913 1612261703885132554626685)
                  ·
                    refine ⟨604598138956924707985007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1612261703885132554626685 604598138956924707985007)
                    ·
                      rfl

theorem cell22_1766176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 3, 2, 3].length) (baseStart_1766176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1766176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1766176 prefixEnd_1766176 := by exact prefixLift 1766176
  have htrace : WordTrace (prefixWord ++ tailWord_1766176) baseStart_1766176 baseEnd_1766176 := by
    simpa [prefixWord, tailWord_1766176, baseEnd_1766176] using wordTrace_append hprefix tailTrace_1766176
  have hstable : (prefixWord ++ tailWord_1766176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766176).length < 2 ^ (prefixWord ++ tailWord_1766176).sum := by decide
  have hdescent : baseEnd_1766176 < baseStart_1766176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766204 : List Nat := [2, 2, 2, 2, 1, 1, 1, 1, 7, 3]
def baseStart_1766204 : Nat := 118140960795 + 1766204 * 2 ^ 59
def prefixEnd_1766204 : Nat := 4983230072969 + 3 ^ 40 * 1766204 * 2
def baseEnd_1766204 : Nat := 604607723929141968284921

theorem tailTrace_1766204 : CollatzResearch.WordTrace tailWord_1766204 prefixEnd_1766204 604607723929141968284921 := by
  unfold tailWord_1766204
  simp only [CollatzResearch.WordTrace]
  refine ⟨32209376046676013236616833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42945834728901350982155777 32209376046676013236616833)
  ·
    refine ⟨24157032035007009927462625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32209376046676013236616833 24157032035007009927462625)
    ·
      refine ⟨18117774026255257445596969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24157032035007009927462625 18117774026255257445596969)
      ·
        refine ⟨13588330519691443084197727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18117774026255257445596969 13588330519691443084197727)
        ·
          refine ⟨20382495779537164626296591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13588330519691443084197727 20382495779537164626296591)
          ·
            refine ⟨30573743669305746939444887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20382495779537164626296591 30573743669305746939444887)
            ·
              refine ⟨45860615503958620409167331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30573743669305746939444887 45860615503958620409167331)
              ·
                refine ⟨68790923255937930613750997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45860615503958620409167331 68790923255937930613750997)
                ·
                  refine ⟨1612287263811045248759789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 68790923255937930613750997 1612287263811045248759789)
                  ·
                    refine ⟨604607723929141968284921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1612287263811045248759789 604607723929141968284921)
                    ·
                      rfl

theorem cell22_1766204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 7, 3].length) (baseStart_1766204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1766204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1766204 prefixEnd_1766204 := by exact prefixLift 1766204
  have htrace : WordTrace (prefixWord ++ tailWord_1766204) baseStart_1766204 baseEnd_1766204 := by
    simpa [prefixWord, tailWord_1766204, baseEnd_1766204] using wordTrace_append hprefix tailTrace_1766204
  have hstable : (prefixWord ++ tailWord_1766204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766204).length < 2 ^ (prefixWord ++ tailWord_1766204).sum := by decide
  have hdescent : baseEnd_1766204 < baseStart_1766204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766328 : List Nat := [2, 1, 2, 1, 2, 5, 2, 2, 2, 3]
def baseStart_1766328 : Nat := 118140960795 + 1766328 * 2 ^ 59
def prefixEnd_1766328 : Nat := 4983230072969 + 3 ^ 40 * 1766328 * 2
def baseEnd_1766328 : Nat := 604650171663246978184541

theorem tailTrace_1766328 : CollatzResearch.WordTrace tailWord_1766328 prefixEnd_1766328 604650171663246978184541 := by
  unfold tailWord_1766328
  simp only [CollatzResearch.WordTrace]
  refine ⟨32211637372451397825373819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42948849829935197100498425 32211637372451397825373819)
  ·
    refine ⟨48317456058677096738060729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32211637372451397825373819 48317456058677096738060729)
    ·
      refine ⟨36238092044007822553545547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48317456058677096738060729 36238092044007822553545547)
      ·
        refine ⟨54357138066011733830318321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36238092044007822553545547 54357138066011733830318321)
        ·
          refine ⟨40767853549508800372738741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54357138066011733830318321 40767853549508800372738741)
          ·
            refine ⟨3821986270266450034944257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40767853549508800372738741 3821986270266450034944257)
            ·
              refine ⟨2866489702699837526208193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3821986270266450034944257 2866489702699837526208193)
              ·
                refine ⟨2149867277024878144656145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2866489702699837526208193 2149867277024878144656145)
                ·
                  refine ⟨1612400457768658608492109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2149867277024878144656145 1612400457768658608492109)
                  ·
                    refine ⟨604650171663246978184541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1612400457768658608492109 604650171663246978184541)
                    ·
                      rfl

theorem cell22_1766328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 2, 2, 3].length) (baseStart_1766328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1766328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1766328 prefixEnd_1766328 := by exact prefixLift 1766328
  have htrace : WordTrace (prefixWord ++ tailWord_1766328) baseStart_1766328 baseEnd_1766328 := by
    simpa [prefixWord, tailWord_1766328, baseEnd_1766328] using wordTrace_append hprefix tailTrace_1766328
  have hstable : (prefixWord ++ tailWord_1766328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766328).length < 2 ^ (prefixWord ++ tailWord_1766328).sum := by decide
  have hdescent : baseEnd_1766328 < baseStart_1766328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766369 : List Nat := [1, 2, 3, 1, 2, 1, 1, 4, 7]
def baseStart_1766369 : Nat := 118140960795 + 1766369 * 2 ^ 59
def prefixEnd_1766369 : Nat := 4983230072969 + 3 ^ 40 * 1766369 * 2
def baseEnd_1766369 : Nat := 201554735600378845969805

theorem tailTrace_1766369 : CollatzResearch.WordTrace tailWord_1766369 prefixEnd_1766369 201554735600378845969805 := by
  unfold tailWord_1766369
  simp only [CollatzResearch.WordTrace]
  refine ⟨64424770137754259652990161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42949846758502839768660107 64424770137754259652990161)
  ·
    refine ⟨48318577603315694739742621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64424770137754259652990161 48318577603315694739742621)
    ·
      refine ⟨18119466601243385527403483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48318577603315694739742621 18119466601243385527403483)
      ·
        refine ⟨27179199901865078291105225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18119466601243385527403483 27179199901865078291105225)
        ·
          refine ⟨20384399926398808718328919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27179199901865078291105225 20384399926398808718328919)
          ·
            refine ⟨30576599889598213077493379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20384399926398808718328919 30576599889598213077493379)
            ·
              refine ⟨45864899834397319616240069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30576599889598213077493379 45864899834397319616240069)
              ·
                refine ⟨8599668718949497428045013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45864899834397319616240069 8599668718949497428045013)
                ·
                  refine ⟨201554735600378845969805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8599668718949497428045013 201554735600378845969805)
                  ·
                    rfl

theorem cell22_1766369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 7].length) (baseStart_1766369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1766369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1766369 prefixEnd_1766369 := by exact prefixLift 1766369
  have htrace : WordTrace (prefixWord ++ tailWord_1766369) baseStart_1766369 baseEnd_1766369 := by
    simpa [prefixWord, tailWord_1766369, baseEnd_1766369] using wordTrace_append hprefix tailTrace_1766369
  have hstable : (prefixWord ++ tailWord_1766369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766369).length < 2 ^ (prefixWord ++ tailWord_1766369).sum := by decide
  have hdescent : baseEnd_1766369 < baseStart_1766369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766390 : List Nat := [5, 1, 1, 1, 3, 2, 2, 1, 3, 3]
def baseStart_1766390 : Nat := 118140960795 + 1766390 * 2 ^ 59
def prefixEnd_1766390 : Nat := 4983230072969 + 3 ^ 40 * 1766390 * 2
def baseEnd_1766390 : Nat := 604671395530299483134351

theorem tailTrace_1766390 : CollatzResearch.WordTrace tailWord_1766390 prefixEnd_1766390 604671395530299483134351 := by
  unfold tailWord_1766390
  simp only [CollatzResearch.WordTrace]
  refine ⟨4026596004417386264969039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42950357380452120159669749 4026596004417386264969039)
  ·
    refine ⟨6039894006626079397453559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4026596004417386264969039 6039894006626079397453559)
    ·
      refine ⟨9059841009939119096180339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6039894006626079397453559 9059841009939119096180339)
      ·
        refine ⟨13589761514908678644270509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9059841009939119096180339 13589761514908678644270509)
        ·
          refine ⟨5096160568090754491601441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13589761514908678644270509 5096160568090754491601441)
          ·
            refine ⟨3822120426068065868701081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5096160568090754491601441 3822120426068065868701081)
            ·
              refine ⟨2866590319551049401525811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3822120426068065868701081 2866590319551049401525811)
              ·
                refine ⟨4299885479326574102288717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2866590319551049401525811 4299885479326574102288717)
                ·
                  refine ⟨1612457054747465288358269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4299885479326574102288717 1612457054747465288358269)
                  ·
                    refine ⟨604671395530299483134351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1612457054747465288358269 604671395530299483134351)
                    ·
                      rfl

theorem cell22_1766390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_1766390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1766390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1766390 prefixEnd_1766390 := by exact prefixLift 1766390
  have htrace : WordTrace (prefixWord ++ tailWord_1766390) baseStart_1766390 baseEnd_1766390 := by
    simpa [prefixWord, tailWord_1766390, baseEnd_1766390] using wordTrace_append hprefix tailTrace_1766390
  have hstable : (prefixWord ++ tailWord_1766390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766390).length < 2 ^ (prefixWord ++ tailWord_1766390).sum := by decide
  have hdescent : baseEnd_1766390 < baseStart_1766390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766401 : List Nat := [1, 2, 4, 1, 2, 2, 2, 1, 2, 5]
def baseStart_1766401 : Nat := 118140960795 + 1766401 * 2 ^ 59
def prefixEnd_1766401 : Nat := 4983230072969 + 3 ^ 40 * 1766401 * 2
def baseEnd_1766401 : Nat := 604675161055099121109317

theorem tailTrace_1766401 : CollatzResearch.WordTrace tailWord_1766401 prefixEnd_1766401 604675161055099121109317 := by
  unfold tailWord_1766401
  simp only [CollatzResearch.WordTrace]
  refine ⟨64425937273638329118155057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42950624849092219412103371 64425937273638329118155057)
  ·
    refine ⟨48319452955228746838616293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64425937273638329118155057 48319452955228746838616293)
    ·
      refine ⟨9059897429105390032240555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48319452955228746838616293 9059897429105390032240555)
      ·
        refine ⟨13589846143658085048360833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9059897429105390032240555 13589846143658085048360833)
        ·
          refine ⟨10192384607743563786270625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13589846143658085048360833 10192384607743563786270625)
          ·
            refine ⟨7644288455807672839702969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10192384607743563786270625 7644288455807672839702969)
            ·
              refine ⟨5733216341855754629777227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7644288455807672839702969 5733216341855754629777227)
              ·
                refine ⟨8599824512783631944665841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5733216341855754629777227 8599824512783631944665841)
                ·
                  refine ⟨6449868384587723958499381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8599824512783631944665841 6449868384587723958499381)
                  ·
                    refine ⟨604675161055099121109317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6449868384587723958499381 604675161055099121109317)
                    ·
                      rfl

theorem cell22_1766401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_1766401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1766401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1766401 prefixEnd_1766401 := by exact prefixLift 1766401
  have htrace : WordTrace (prefixWord ++ tailWord_1766401) baseStart_1766401 baseEnd_1766401 := by
    simpa [prefixWord, tailWord_1766401, baseEnd_1766401] using wordTrace_append hprefix tailTrace_1766401
  have hstable : (prefixWord ++ tailWord_1766401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766401).length < 2 ^ (prefixWord ++ tailWord_1766401).sum := by decide
  have hdescent : baseEnd_1766401 < baseStart_1766401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766433 : List Nat := [1, 2, 3, 2, 3, 1, 2, 3, 1, 4]
def baseStart_1766433 : Nat := 118140960795 + 1766433 * 2 ^ 59
def prefixEnd_1766433 : Nat := 4983230072969 + 3 ^ 40 * 1766433 * 2
def baseEnd_1766433 : Nat := 604686115309061704309219

theorem tailTrace_1766433 : CollatzResearch.WordTrace tailWord_1766433 prefixEnd_1766433 604686115309061704309219 := by
  unfold tailWord_1766433
  simp only [CollatzResearch.WordTrace]
  refine ⟨64427104409522398583319953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42951402939681599055546635 64427104409522398583319953)
  ·
    refine ⟨48320328307141798937489965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64427104409522398583319953 48320328307141798937489965)
    ·
      refine ⟨18120123115178174601558737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48320328307141798937489965 18120123115178174601558737)
      ·
        refine ⟨13590092336383630951169053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18120123115178174601558737 13590092336383630951169053)
        ·
          refine ⟨5096284626143861606688395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13590092336383630951169053 5096284626143861606688395)
          ·
            refine ⟨7644426939215792410032593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5096284626143861606688395 7644426939215792410032593)
            ·
              refine ⟨5733320204411844307524445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7644426939215792410032593 5733320204411844307524445)
              ·
                refine ⟨2149995076654441615321667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5733320204411844307524445 2149995076654441615321667)
                ·
                  refine ⟨3224992614981662422982501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2149995076654441615321667 3224992614981662422982501)
                  ·
                    refine ⟨604686115309061704309219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3224992614981662422982501 604686115309061704309219)
                    ·
                      rfl

theorem cell22_1766433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 3, 1, 4].length) (baseStart_1766433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1766433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1766433 prefixEnd_1766433 := by exact prefixLift 1766433
  have htrace : WordTrace (prefixWord ++ tailWord_1766433) baseStart_1766433 baseEnd_1766433 := by
    simpa [prefixWord, tailWord_1766433, baseEnd_1766433] using wordTrace_append hprefix tailTrace_1766433
  have hstable : (prefixWord ++ tailWord_1766433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766433).length < 2 ^ (prefixWord ++ tailWord_1766433).sum := by decide
  have hdescent : baseEnd_1766433 < baseStart_1766433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766478 : List Nat := [4, 1, 1, 1, 1, 3, 4, 1, 2, 4]
def baseStart_1766478 : Nat := 118140960795 + 1766478 * 2 ^ 59
def prefixEnd_1766478 : Nat := 4983230072969 + 3 ^ 40 * 1766478 * 2
def baseEnd_1766478 : Nat := 604701519728696586934081

theorem tailTrace_1766478 : CollatzResearch.WordTrace tailWord_1766478 prefixEnd_1766478 604701519728696586934081 := by
  unfold tailWord_1766478
  simp only [CollatzResearch.WordTrace]
  refine ⟨8053593211794921408588511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42952497129572914179138725 8053593211794921408588511)
  ·
    refine ⟨12080389817692382112882767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8053593211794921408588511 12080389817692382112882767)
    ·
      refine ⟨18120584726538573169324151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12080389817692382112882767 18120584726538573169324151)
      ·
        refine ⟨27180877089807859753986227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18120584726538573169324151 27180877089807859753986227)
        ·
          refine ⟨40771315634711789630979341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27180877089807859753986227 40771315634711789630979341)
          ·
            refine ⟨15289243363016921111617253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40771315634711789630979341 15289243363016921111617253)
            ·
              refine ⟨2866733130565672708428235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15289243363016921111617253 2866733130565672708428235)
              ·
                refine ⟨4300099695848509062642353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2866733130565672708428235 4300099695848509062642353)
                ·
                  refine ⟨3225074771886381796981765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4300099695848509062642353 3225074771886381796981765)
                  ·
                    refine ⟨604701519728696586934081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3225074771886381796981765 604701519728696586934081)
                    ·
                      rfl

theorem cell22_1766478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 1, 2, 4].length) (baseStart_1766478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1766478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1766478 prefixEnd_1766478 := by exact prefixLift 1766478
  have htrace : WordTrace (prefixWord ++ tailWord_1766478) baseStart_1766478 baseEnd_1766478 := by
    simpa [prefixWord, tailWord_1766478, baseEnd_1766478] using wordTrace_append hprefix tailTrace_1766478
  have hstable : (prefixWord ++ tailWord_1766478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766478).length < 2 ^ (prefixWord ++ tailWord_1766478).sum := by decide
  have hdescent : baseEnd_1766478 < baseStart_1766478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766493 : List Nat := [1, 4, 4, 1, 2, 10]
def baseStart_1766493 : Nat := 118140960795 + 1766493 * 2 ^ 59
def prefixEnd_1766493 : Nat := 4983230072969 + 3 ^ 40 * 1766493 * 2
def baseEnd_1766493 : Nat := 7465514253521500590235

theorem tailTrace_1766493 : CollatzResearch.WordTrace tailWord_1766493 prefixEnd_1766493 7465514253521500590235 := by
  unfold tailWord_1766493
  simp only [CollatzResearch.WordTrace]
  refine ⟨64429292789305028830504133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42952861859536685887002755 64429292789305028830504133)
  ·
    refine ⟨12080492397994692905719525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64429292789305028830504133 12080492397994692905719525)
    ·
      refine ⟨2265092324624004919822411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12080492397994692905719525 2265092324624004919822411)
      ·
        refine ⟨3397638486936007379733617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2265092324624004919822411 3397638486936007379733617)
        ·
          refine ⟨2548228865202005534800213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3397638486936007379733617 2548228865202005534800213)
          ·
            refine ⟨7465514253521500590235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2548228865202005534800213 7465514253521500590235)
            ·
              rfl

theorem cell22_1766493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 10].length) (baseStart_1766493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1766493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1766493 prefixEnd_1766493 := by exact prefixLift 1766493
  have htrace : WordTrace (prefixWord ++ tailWord_1766493) baseStart_1766493 baseEnd_1766493 := by
    simpa [prefixWord, tailWord_1766493, baseEnd_1766493] using wordTrace_append hprefix tailTrace_1766493
  have hstable : (prefixWord ++ tailWord_1766493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766493).length < 2 ^ (prefixWord ++ tailWord_1766493).sum := by decide
  have hdescent : baseEnd_1766493 < baseStart_1766493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766508 : List Nat := [2, 2, 1, 1, 3, 2, 2, 3, 3, 3]
def baseStart_1766508 : Nat := 118140960795 + 1766508 * 2 ^ 59
def prefixEnd_1766508 : Nat := 4983230072969 + 3 ^ 40 * 1766508 * 2
def baseEnd_1766508 : Nat := 604711789341786508683989

theorem tailTrace_1766508 : CollatzResearch.WordTrace tailWord_1766508 prefixEnd_1766508 604711789341786508683989 := by
  unfold tailWord_1766508
  simp only [CollatzResearch.WordTrace]
  refine ⟨32214919942125343196150089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42953226589500457594866785 32214919942125343196150089)
  ·
    refine ⟨24161189956594007397112567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32214919942125343196150089 24161189956594007397112567)
    ·
      refine ⟨36241784934891011095668851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24161189956594007397112567 36241784934891011095668851)
      ·
        refine ⟨54362677402336516643503277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36241784934891011095668851 54362677402336516643503277)
        ·
          refine ⟨20386004025876193741313729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54362677402336516643503277 20386004025876193741313729)
          ·
            refine ⟨15289503019407145305985297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20386004025876193741313729 15289503019407145305985297)
            ·
              refine ⟨11467127264555358979488973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15289503019407145305985297 11467127264555358979488973)
              ·
                refine ⟨4300172724208259617308365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11467127264555358979488973 4300172724208259617308365)
                ·
                  refine ⟨1612564771578097356490637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4300172724208259617308365 1612564771578097356490637)
                  ·
                    refine ⟨604711789341786508683989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1612564771578097356490637 604711789341786508683989)
                    ·
                      rfl

theorem cell22_1766508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 3].length) (baseStart_1766508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1766508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1766508 prefixEnd_1766508 := by exact prefixLift 1766508
  have htrace : WordTrace (prefixWord ++ tailWord_1766508) baseStart_1766508 baseEnd_1766508 := by
    simpa [prefixWord, tailWord_1766508, baseEnd_1766508] using wordTrace_append hprefix tailTrace_1766508
  have hstable : (prefixWord ++ tailWord_1766508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766508).length < 2 ^ (prefixWord ++ tailWord_1766508).sum := by decide
  have hdescent : baseEnd_1766508 < baseStart_1766508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766542 : List Nat := [4, 1, 1, 3, 2, 1, 1, 5, 1, 3]
def baseStart_1766542 : Nat := 118140960795 + 1766542 * 2 ^ 59
def prefixEnd_1766542 : Nat := 4983230072969 + 3 ^ 40 * 1766542 * 2
def baseEnd_1766542 : Nat := 604723428236621753333885

theorem tailTrace_1766542 : CollatzResearch.WordTrace tailWord_1766542 prefixEnd_1766542 604723428236621753333885 := by
  unfold tailWord_1766542
  simp only [CollatzResearch.WordTrace]
  refine ⟨8053884995765938774879735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42954053310751673466025253 8053884995765938774879735)
  ·
    refine ⟨12080827493648908162319603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8053884995765938774879735 12080827493648908162319603)
    ·
      refine ⟨18121241240473362243479405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12080827493648908162319603 18121241240473362243479405)
      ·
        refine ⟨6795465465177510841304777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18121241240473362243479405 6795465465177510841304777)
        ·
          refine ⟨5096599098883133130978583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6795465465177510841304777 5096599098883133130978583)
          ·
            refine ⟨7644898648324699696467875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5096599098883133130978583 7644898648324699696467875)
            ·
              refine ⟨11467347972487049544701813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7644898648324699696467875 11467347972487049544701813)
              ·
                refine ⟨1075063872420660894815795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11467347972487049544701813 1075063872420660894815795)
                ·
                  refine ⟨1612595808630991342223693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1075063872420660894815795 1612595808630991342223693)
                  ·
                    refine ⟨604723428236621753333885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1612595808630991342223693 604723428236621753333885)
                    ·
                      rfl

theorem cell22_1766542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 5, 1, 3].length) (baseStart_1766542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1766542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1766542 prefixEnd_1766542 := by exact prefixLift 1766542
  have htrace : WordTrace (prefixWord ++ tailWord_1766542) baseStart_1766542 baseEnd_1766542 := by
    simpa [prefixWord, tailWord_1766542, baseEnd_1766542] using wordTrace_append hprefix tailTrace_1766542
  have hstable : (prefixWord ++ tailWord_1766542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766542).length < 2 ^ (prefixWord ++ tailWord_1766542).sum := by decide
  have hdescent : baseEnd_1766542 < baseStart_1766542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766570 : List Nat := [3, 1, 5, 1, 1, 1, 2, 1, 2, 5]
def baseStart_1766570 : Nat := 118140960795 + 1766570 * 2 ^ 59
def prefixEnd_1766570 : Nat := 4983230072969 + 3 ^ 40 * 1766570 * 2
def baseEnd_1766570 : Nat := 604733013208839013633799

theorem tailTrace_1766570 : CollatzResearch.WordTrace tailWord_1766570 prefixEnd_1766570 604733013208839013633799 := by
  unfold tailWord_1766570
  simp only [CollatzResearch.WordTrace]
  refine ⟨16108025302506517745264291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42954734140017380654038109 16108025302506517745264291)
  ·
    refine ⟨24162037953759776617896437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16108025302506517745264291 24162037953759776617896437)
    ·
      refine ⟨2265191058164979057927791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24162037953759776617896437 2265191058164979057927791)
      ·
        refine ⟨3397786587247468586891687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2265191058164979057927791 3397786587247468586891687)
        ·
          refine ⟨5096679880871202880337531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3397786587247468586891687 5096679880871202880337531)
          ·
            refine ⟨7645019821306804320506297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5096679880871202880337531 7645019821306804320506297)
            ·
              refine ⟨5733764865980103240379723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7645019821306804320506297 5733764865980103240379723)
              ·
                refine ⟨8600647298970154860569585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5733764865980103240379723 8600647298970154860569585)
                ·
                  refine ⟨6450485474227616145427189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8600647298970154860569585 6450485474227616145427189)
                  ·
                    refine ⟨604733013208839013633799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6450485474227616145427189 604733013208839013633799)
                    ·
                      rfl

theorem cell22_1766570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_1766570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1766570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1766570 prefixEnd_1766570 := by exact prefixLift 1766570
  have htrace : WordTrace (prefixWord ++ tailWord_1766570) baseStart_1766570 baseEnd_1766570 := by
    simpa [prefixWord, tailWord_1766570, baseEnd_1766570] using wordTrace_append hprefix tailTrace_1766570
  have hstable : (prefixWord ++ tailWord_1766570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766570).length < 2 ^ (prefixWord ++ tailWord_1766570).sum := by decide
  have hdescent : baseEnd_1766570 < baseStart_1766570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766585 : List Nat := [1, 2, 1, 4, 1, 4, 2, 2, 1, 4]
def baseStart_1766585 : Nat := 118140960795 + 1766585 * 2 ^ 59
def prefixEnd_1766585 : Nat := 4983230072969 + 3 ^ 40 * 1766585 * 2
def baseEnd_1766585 : Nat := 604738148015383974508753

theorem tailTrace_1766585 : CollatzResearch.WordTrace tailWord_1766585 prefixEnd_1766585 604738148015383974508753 := by
  unfold tailWord_1766585
  simp only [CollatzResearch.WordTrace]
  refine ⟨64432648304971728542853209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42955098869981152361902139 64432648304971728542853209)
  ·
    refine ⟨48324486228728796407139907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64432648304971728542853209 48324486228728796407139907)
    ·
      refine ⟨72486729343093194610709861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48324486228728796407139907 72486729343093194610709861)
      ·
        refine ⟨13591261751829973989508099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72486729343093194610709861 13591261751829973989508099)
        ·
          refine ⟨20386892627744960984262149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13591261751829973989508099 20386892627744960984262149)
          ·
            refine ⟨3822542367702180184549153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20386892627744960984262149 3822542367702180184549153)
            ·
              refine ⟨2866906775776635138411865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3822542367702180184549153 2866906775776635138411865)
              ·
                refine ⟨2150180081832476353808899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2866906775776635138411865 2150180081832476353808899)
                ·
                  refine ⟨3225270122748714530713349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2150180081832476353808899 3225270122748714530713349)
                  ·
                    refine ⟨604738148015383974508753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3225270122748714530713349 604738148015383974508753)
                    ·
                      rfl

theorem cell22_1766585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 2, 1, 4].length) (baseStart_1766585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1766585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1766585 prefixEnd_1766585 := by exact prefixLift 1766585
  have htrace : WordTrace (prefixWord ++ tailWord_1766585) baseStart_1766585 baseEnd_1766585 := by
    simpa [prefixWord, tailWord_1766585, baseEnd_1766585] using wordTrace_append hprefix tailTrace_1766585
  have hstable : (prefixWord ++ tailWord_1766585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766585).length < 2 ^ (prefixWord ++ tailWord_1766585).sum := by decide
  have hdescent : baseEnd_1766585 < baseStart_1766585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766600 : List Nat := [2, 1, 3, 1, 2, 1, 5, 3, 4]
def baseStart_1766600 : Nat := 118140960795 + 1766600 * 2 ^ 59
def prefixEnd_1766600 : Nat := 4983230072969 + 3 ^ 40 * 1766600 * 2
def baseEnd_1766600 : Nat := 201581094273976311794569

theorem tailTrace_1766600 : CollatzResearch.WordTrace tailWord_1766600 prefixEnd_1766600 201581094273976311794569 := by
  unfold tailWord_1766600
  simp only [CollatzResearch.WordTrace]
  refine ⟨32216597699958693052324627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42955463599944924069766169 32216597699958693052324627)
  ·
    refine ⟨48324896549938039578486941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32216597699958693052324627 48324896549938039578486941)
    ·
      refine ⟨18121836206226764841932603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48324896549938039578486941 18121836206226764841932603)
      ·
        refine ⟨27182754309340147262898905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18121836206226764841932603 27182754309340147262898905)
        ·
          refine ⟨20387065732005110447174179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27182754309340147262898905 20387065732005110447174179)
          ·
            refine ⟨30580598598007665670761269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20387065732005110447174179 30580598598007665670761269)
            ·
              refine ⟨2866931118563218656633869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30580598598007665670761269 2866931118563218656633869)
              ·
                refine ⟨1075099169461206996237701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2866931118563218656633869 1075099169461206996237701)
                ·
                  refine ⟨201581094273976311794569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1075099169461206996237701 201581094273976311794569)
                  ·
                    rfl

theorem cell22_1766600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 3, 4].length) (baseStart_1766600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1766600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1766600 prefixEnd_1766600 := by exact prefixLift 1766600
  have htrace : WordTrace (prefixWord ++ tailWord_1766600) baseStart_1766600 baseEnd_1766600 := by
    simpa [prefixWord, tailWord_1766600, baseEnd_1766600] using wordTrace_append hprefix tailTrace_1766600
  have hstable : (prefixWord ++ tailWord_1766600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766600).length < 2 ^ (prefixWord ++ tailWord_1766600).sum := by decide
  have hdescent : baseEnd_1766600 < baseStart_1766600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766720 : List Nat := [2, 1, 1, 2, 2, 1, 5, 3, 1, 4]
def baseStart_1766720 : Nat := 118140960795 + 1766720 * 2 ^ 59
def prefixEnd_1766720 : Nat := 4983230072969 + 3 ^ 40 * 1766720 * 2
def baseEnd_1766720 : Nat := 604784361274288622383339

theorem tailTrace_1766720 : CollatzResearch.WordTrace tailWord_1766720 prefixEnd_1766720 604784361274288622383339 := by
  unfold tailWord_1766720
  simp only [CollatzResearch.WordTrace]
  refine ⟨32218786079741323299508807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42958381439655097732678409 32218786079741323299508807)
  ·
    refine ⟨48328179119611984949263211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32218786079741323299508807 48328179119611984949263211)
    ·
      refine ⟨72492268679417977423894817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48328179119611984949263211 72492268679417977423894817)
      ·
        refine ⟨54369201509563483067921113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72492268679417977423894817 54369201509563483067921113)
        ·
          refine ⟨40776901132172612300940835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54369201509563483067921113 40776901132172612300940835)
          ·
            refine ⟨61165351698258918451411253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40776901132172612300940835 61165351698258918451411253)
            ·
              refine ⟨5734251721711773604819805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61165351698258918451411253 5734251721711773604819805)
              ·
                refine ⟨2150344395641915101807427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5734251721711773604819805 2150344395641915101807427)
                ·
                  refine ⟨3225516593462872652711141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2150344395641915101807427 3225516593462872652711141)
                  ·
                    refine ⟨604784361274288622383339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3225516593462872652711141 604784361274288622383339)
                    ·
                      rfl

theorem cell22_1766720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 3, 1, 4].length) (baseStart_1766720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1766720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1766720 prefixEnd_1766720 := by exact prefixLift 1766720
  have htrace : WordTrace (prefixWord ++ tailWord_1766720) baseStart_1766720 baseEnd_1766720 := by
    simpa [prefixWord, tailWord_1766720, baseEnd_1766720] using wordTrace_append hprefix tailTrace_1766720
  have hstable : (prefixWord ++ tailWord_1766720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766720).length < 2 ^ (prefixWord ++ tailWord_1766720).sum := by decide
  have hdescent : baseEnd_1766720 < baseStart_1766720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766724 : List Nat := [2, 3, 4, 1, 1, 3, 1, 2, 5]
def baseStart_1766724 : Nat := 118140960795 + 1766724 * 2 ^ 59
def prefixEnd_1766724 : Nat := 4983230072969 + 3 ^ 40 * 1766724 * 2
def baseEnd_1766724 : Nat := 201595243518677981761109

theorem tailTrace_1766724 : CollatzResearch.WordTrace tailWord_1766724 prefixEnd_1766724 201595243518677981761109 := by
  unfold tailWord_1766724
  simp only [CollatzResearch.WordTrace]
  refine ⟨32218859025734077641081613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42958478700978770188108817 32218859025734077641081613)
  ·
    refine ⟨12082072134650279115405605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32218859025734077641081613 12082072134650279115405605)
    ·
      refine ⟨2265388525246927334138551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12082072134650279115405605 2265388525246927334138551)
      ·
        refine ⟨3398082787870391001207827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2265388525246927334138551 3398082787870391001207827)
        ·
          refine ⟨5097124181805586501811741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3398082787870391001207827 5097124181805586501811741)
          ·
            refine ⟨1911421568177094938179403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5097124181805586501811741 1911421568177094938179403)
            ·
              refine ⟨2867132352265642407269105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1911421568177094938179403 2867132352265642407269105)
              ·
                refine ⟨2150349264199231805451829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2867132352265642407269105 2150349264199231805451829)
                ·
                  refine ⟨201595243518677981761109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2150349264199231805451829 201595243518677981761109)
                  ·
                    rfl

theorem cell22_1766724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 2, 5].length) (baseStart_1766724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1766724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1766724 prefixEnd_1766724 := by exact prefixLift 1766724
  have htrace : WordTrace (prefixWord ++ tailWord_1766724) baseStart_1766724 baseEnd_1766724 := by
    simpa [prefixWord, tailWord_1766724, baseEnd_1766724] using wordTrace_append hprefix tailTrace_1766724
  have hstable : (prefixWord ++ tailWord_1766724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766724).length < 2 ^ (prefixWord ++ tailWord_1766724).sum := by decide
  have hdescent : baseEnd_1766724 < baseStart_1766724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766765 : List Nat := [1, 5, 1, 1, 1, 3, 2, 1, 1, 6]
def baseStart_1766765 : Nat := 118140960795 + 1766765 * 2 ^ 59
def prefixEnd_1766765 : Nat := 4983230072969 + 3 ^ 40 * 1766765 * 2
def baseEnd_1766765 : Nat := 604799765693923505008201

theorem tailTrace_1766765 : CollatzResearch.WordTrace tailWord_1766765 prefixEnd_1766765 604799765693923505008201 := by
  unfold tailWord_1766765
  simp only [CollatzResearch.WordTrace]
  refine ⟨64439213444319619284405749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42959475629546412856270499 64439213444319619284405749)
  ·
    refine ⟨6041176260404964307913039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64439213444319619284405749 6041176260404964307913039)
    ·
      refine ⟨9061764390607446461869559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6041176260404964307913039 9061764390607446461869559)
      ·
        refine ⟨13592646585911169692804339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9061764390607446461869559 13592646585911169692804339)
        ·
          refine ⟨20388969878866754539206509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13592646585911169692804339 20388969878866754539206509)
          ·
            refine ⟨7645863704575032952202441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20388969878866754539206509 7645863704575032952202441)
            ·
              refine ⟨5734397778431274714151831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7645863704575032952202441 5734397778431274714151831)
              ·
                refine ⟨8601596667646912071227747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5734397778431274714151831 8601596667646912071227747)
                ·
                  refine ⟨12902395001470368106841621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8601596667646912071227747 12902395001470368106841621)
                  ·
                    refine ⟨604799765693923505008201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12902395001470368106841621 604799765693923505008201)
                    ·
                      rfl

theorem cell22_1766765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_1766765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1766765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1766765 prefixEnd_1766765 := by exact prefixLift 1766765
  have htrace : WordTrace (prefixWord ++ tailWord_1766765) baseStart_1766765 baseEnd_1766765 := by
    simpa [prefixWord, tailWord_1766765, baseEnd_1766765] using wordTrace_append hprefix tailTrace_1766765
  have hstable : (prefixWord ++ tailWord_1766765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766765).length < 2 ^ (prefixWord ++ tailWord_1766765).sum := by decide
  have hdescent : baseEnd_1766765 < baseStart_1766765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766778 : List Nat := [3, 1, 1, 1, 1, 1, 2, 2, 1, 9]
def baseStart_1766778 : Nat := 118140960795 + 1766778 * 2 ^ 59
def prefixEnd_1766778 : Nat := 4983230072969 + 3 ^ 40 * 1766778 * 2
def baseEnd_1766778 : Nat := 604804215859595804433161

theorem tailTrace_1766778 : CollatzResearch.WordTrace tailWord_1766778 prefixEnd_1766778 604804215859595804433161 := by
  unfold tailWord_1766778
  simp only [CollatzResearch.WordTrace]
  refine ⟨16109921898318130626157247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42959791728848348336419325 16109921898318130626157247)
  ·
    refine ⟨24164882847477195939235871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16109921898318130626157247 24164882847477195939235871)
    ·
      refine ⟨36247324271215793908853807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24164882847477195939235871 36247324271215793908853807)
      ·
        refine ⟨54370986406823690863280711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36247324271215793908853807 54370986406823690863280711)
        ·
          refine ⟨81556479610235536294921067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54370986406823690863280711 81556479610235536294921067)
          ·
            refine ⟨122334719415353304442381601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81556479610235536294921067 122334719415353304442381601)
            ·
              refine ⟨91751039561514978331786201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122334719415353304442381601 91751039561514978331786201)
              ·
                refine ⟨68813279671136233748839651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91751039561514978331786201 68813279671136233748839651)
                ·
                  refine ⟨103219919506704350623259477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68813279671136233748839651 103219919506704350623259477)
                  ·
                    refine ⟨604804215859595804433161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 103219919506704350623259477 604804215859595804433161)
                    ·
                      rfl

theorem cell22_1766778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 1, 9].length) (baseStart_1766778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1766778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1766778 prefixEnd_1766778 := by exact prefixLift 1766778
  have htrace : WordTrace (prefixWord ++ tailWord_1766778) baseStart_1766778 baseEnd_1766778 := by
    simpa [prefixWord, tailWord_1766778, baseEnd_1766778] using wordTrace_append hprefix tailTrace_1766778
  have hstable : (prefixWord ++ tailWord_1766778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766778).length < 2 ^ (prefixWord ++ tailWord_1766778).sum := by decide
  have hdescent : baseEnd_1766778 < baseStart_1766778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766855 : List Nat := [1, 1, 4, 1, 1, 3, 1, 1, 5, 4]
def baseStart_1766855 : Nat := 118140960795 + 1766855 * 2 ^ 59
def prefixEnd_1766855 : Nat := 4983230072969 + 3 ^ 40 * 1766855 * 2
def baseEnd_1766855 : Nat := 604830574533193270257925

theorem tailTrace_1766855 : CollatzResearch.WordTrace tailWord_1766855 prefixEnd_1766855 604830574533193270257925 := by
  unfold tailWord_1766855
  simp only [CollatzResearch.WordTrace]
  refine ⟨64442496013993564655182019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42961664009329043103454679 64442496013993564655182019)
  ·
    refine ⟨96663744020990346982773029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64442496013993564655182019 96663744020990346982773029)
    ·
      refine ⟨18124452003935690059269943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96663744020990346982773029 18124452003935690059269943)
      ·
        refine ⟨27186678005903535088904915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18124452003935690059269943 27186678005903535088904915)
        ·
          refine ⟨40780017008855302633357373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27186678005903535088904915 40780017008855302633357373)
          ·
            refine ⟨15292506378320738487509015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40780017008855302633357373 15292506378320738487509015)
            ·
              refine ⟨22938759567481107731263523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15292506378320738487509015 22938759567481107731263523)
              ·
                refine ⟨34408139351221661596895285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22938759567481107731263523 34408139351221661596895285)
                ·
                  refine ⟨3225763064177030774708933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34408139351221661596895285 3225763064177030774708933)
                  ·
                    refine ⟨604830574533193270257925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3225763064177030774708933 604830574533193270257925)
                    ·
                      rfl

theorem cell22_1766855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_1766855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1766855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1766855 prefixEnd_1766855 := by exact prefixLift 1766855
  have htrace : WordTrace (prefixWord ++ tailWord_1766855) baseStart_1766855 baseEnd_1766855 := by
    simpa [prefixWord, tailWord_1766855, baseEnd_1766855] using wordTrace_append hprefix tailTrace_1766855
  have hstable : (prefixWord ++ tailWord_1766855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766855).length < 2 ^ (prefixWord ++ tailWord_1766855).sum := by decide
  have hdescent : baseEnd_1766855 < baseStart_1766855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766919 : List Nat := [1, 1, 4, 3, 2, 3, 1, 1, 1, 5]
def baseStart_1766919 : Nat := 118140960795 + 1766919 * 2 ^ 59
def prefixEnd_1766919 : Nat := 4983230072969 + 3 ^ 40 * 1766919 * 2
def baseEnd_1766919 : Nat := 604852483041118436657729

theorem tailTrace_1766919 : CollatzResearch.WordTrace tailWord_1766919 prefixEnd_1766919 604852483041118436657729 := by
  unfold tailWord_1766919
  simp only [CollatzResearch.WordTrace]
  refine ⟨64444830285761703585511811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42963220190507802390341207 64444830285761703585511811)
  ·
    refine ⟨96667245428642555378267717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64444830285761703585511811 96667245428642555378267717)
    ·
      refine ⟨18125108517870479133425197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96667245428642555378267717 18125108517870479133425197)
      ·
        refine ⟨6796915694201429675034449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18125108517870479133425197 6796915694201429675034449)
        ·
          refine ⟨5097686770651072256275837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6796915694201429675034449 5097686770651072256275837)
          ·
            refine ⟨1911632538994152096103439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5097686770651072256275837 1911632538994152096103439)
            ·
              refine ⟨2867448808491228144155159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1911632538994152096103439 2867448808491228144155159)
              ·
                refine ⟨4301173212736842216232739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2867448808491228144155159 4301173212736842216232739)
                ·
                  refine ⟨6451759819105263324349109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4301173212736842216232739 6451759819105263324349109)
                  ·
                    refine ⟨604852483041118436657729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6451759819105263324349109 604852483041118436657729)
                    ·
                      rfl

theorem cell22_1766919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 1, 1, 5].length) (baseStart_1766919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1766919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1766919 prefixEnd_1766919 := by exact prefixLift 1766919
  have htrace : WordTrace (prefixWord ++ tailWord_1766919) baseStart_1766919 baseEnd_1766919 := by
    simpa [prefixWord, tailWord_1766919, baseEnd_1766919] using wordTrace_append hprefix tailTrace_1766919
  have hstable : (prefixWord ++ tailWord_1766919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766919).length < 2 ^ (prefixWord ++ tailWord_1766919).sum := by decide
  have hdescent : baseEnd_1766919 < baseStart_1766919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767052 : List Nat := [2, 2, 1, 2, 1, 1, 5, 1, 1, 6]
def baseStart_1767052 : Nat := 118140960795 + 1767052 * 2 ^ 59
def prefixEnd_1767052 : Nat := 4983230072969 + 3 ^ 40 * 1767052 * 2
def baseEnd_1767052 : Nat := 604898011659150423082321

theorem tailTrace_1767052 : CollatzResearch.WordTrace tailWord_1767052 prefixEnd_1767052 604898011659150423082321 := by
  unfold tailWord_1767052
  simp only [CollatzResearch.WordTrace]
  refine ⟨32224840597139933650051705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42966454129519911533402273 32224840597139933650051705)
  ·
    refine ⟨24168630447854950237538779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32224840597139933650051705 24168630447854950237538779)
    ·
      refine ⟨36252945671782425356308169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24168630447854950237538779 36252945671782425356308169)
      ·
        refine ⟨27189709253836819017231127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36252945671782425356308169 27189709253836819017231127)
        ·
          refine ⟨40784563880755228525846691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27189709253836819017231127 40784563880755228525846691)
          ·
            refine ⟨61176845821132842788770037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40784563880755228525846691 61176845821132842788770037)
            ·
              refine ⟨5735329295731204011447191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61176845821132842788770037 5735329295731204011447191)
              ·
                refine ⟨8602993943596806017170787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5735329295731204011447191 8602993943596806017170787)
                ·
                  refine ⟨12904490915395209025756181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8602993943596806017170787 12904490915395209025756181)
                  ·
                    refine ⟨604898011659150423082321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12904490915395209025756181 604898011659150423082321)
                    ·
                      rfl

theorem cell22_1767052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 1, 6].length) (baseStart_1767052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1767052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1767052 prefixEnd_1767052 := by exact prefixLift 1767052
  have htrace : WordTrace (prefixWord ++ tailWord_1767052) baseStart_1767052 baseEnd_1767052 := by
    simpa [prefixWord, tailWord_1767052, baseEnd_1767052] using wordTrace_append hprefix tailTrace_1767052
  have hstable : (prefixWord ++ tailWord_1767052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767052).length < 2 ^ (prefixWord ++ tailWord_1767052).sum := by decide
  have hdescent : baseEnd_1767052 < baseStart_1767052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767054 : List Nat := [4, 1, 1, 3, 1, 2, 2, 2, 1, 5]
def baseStart_1767054 : Nat := 118140960795 + 1767054 * 2 ^ 59
def prefixEnd_1767054 : Nat := 4983230072969 + 3 ^ 40 * 1767054 * 2
def baseEnd_1767054 : Nat := 604898696300023084532315

theorem tailTrace_1767054 : CollatzResearch.WordTrace tailWord_1767054 prefixEnd_1767054 604898696300023084532315 := by
  unfold tailWord_1767054
  simp only [CollatzResearch.WordTrace]
  refine ⟨8056219267534077705209527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42966502760181747761117477 8056219267534077705209527)
  ·
    refine ⟨12084328901301116557814291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8056219267534077705209527 12084328901301116557814291)
    ·
      refine ⟨18126493351951674836721437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12084328901301116557814291 18126493351951674836721437)
      ·
        refine ⟨6797435006981878063770539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18126493351951674836721437 6797435006981878063770539)
        ·
          refine ⟨10196152510472817095655809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6797435006981878063770539 10196152510472817095655809)
          ·
            refine ⟨7647114382854612821741857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10196152510472817095655809 7647114382854612821741857)
            ·
              refine ⟨5735335787140959616306393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7647114382854612821741857 5735335787140959616306393)
              ·
                refine ⟨4301501840355719712229795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5735335787140959616306393 4301501840355719712229795)
                ·
                  refine ⟨6452252760533579568344693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4301501840355719712229795 6452252760533579568344693)
                  ·
                    refine ⟨604898696300023084532315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6452252760533579568344693 604898696300023084532315)
                    ·
                      rfl

theorem cell22_1767054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_1767054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1767054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1767054 prefixEnd_1767054 := by exact prefixLift 1767054
  have htrace : WordTrace (prefixWord ++ tailWord_1767054) baseStart_1767054 baseEnd_1767054 := by
    simpa [prefixWord, tailWord_1767054, baseEnd_1767054] using wordTrace_append hprefix tailTrace_1767054
  have hstable : (prefixWord ++ tailWord_1767054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767054).length < 2 ^ (prefixWord ++ tailWord_1767054).sum := by decide
  have hdescent : baseEnd_1767054 < baseStart_1767054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767097 : List Nat := [1, 2, 1, 4, 1, 1, 2, 2, 2, 6]
def baseStart_1767097 : Nat := 118140960795 + 1767097 * 2 ^ 59
def prefixEnd_1767097 : Nat := 4983230072969 + 3 ^ 40 * 1767097 * 2
def baseEnd_1767097 : Nat := 604913416078785305707183

theorem tailTrace_1767097 : CollatzResearch.WordTrace tailWord_1767097 prefixEnd_1767097 604913416078785305707183 := by
  unfold tailWord_1767097
  simp only [CollatzResearch.WordTrace]
  refine ⟨64451322479116839985491545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42967548319411226656994363 64451322479116839985491545)
  ·
    refine ⟨48338491859337629989118659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64451322479116839985491545 48338491859337629989118659)
    ·
      refine ⟨72507737789006444983677989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48338491859337629989118659 72507737789006444983677989)
      ·
        refine ⟨13595200835438708434439623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72507737789006444983677989 13595200835438708434439623)
        ·
          refine ⟨20392801253158062651659435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13595200835438708434439623 20392801253158062651659435)
          ·
            refine ⟨30589201879737093977489153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20392801253158062651659435 30589201879737093977489153)
            ·
              refine ⟨22941901409802820483116865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30589201879737093977489153 22941901409802820483116865)
              ·
                refine ⟨17206426057352115362337649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22941901409802820483116865 17206426057352115362337649)
                ·
                  refine ⟨12904819543014086521753237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17206426057352115362337649 12904819543014086521753237)
                  ·
                    refine ⟨604913416078785305707183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12904819543014086521753237 604913416078785305707183)
                    ·
                      rfl

theorem cell22_1767097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 6].length) (baseStart_1767097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1767097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1767097 prefixEnd_1767097 := by exact prefixLift 1767097
  have htrace : WordTrace (prefixWord ++ tailWord_1767097) baseStart_1767097 baseEnd_1767097 := by
    simpa [prefixWord, tailWord_1767097, baseEnd_1767097] using wordTrace_append hprefix tailTrace_1767097
  have hstable : (prefixWord ++ tailWord_1767097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767097).length < 2 ^ (prefixWord ++ tailWord_1767097).sum := by decide
  have hdescent : baseEnd_1767097 < baseStart_1767097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767112 : List Nat := [2, 1, 3, 1, 2, 2, 1, 1, 9]
def baseStart_1767112 : Nat := 118140960795 + 1767112 * 2 ^ 59
def prefixEnd_1767112 : Nat := 4983230072969 + 3 ^ 40 * 1767112 * 2
def baseEnd_1767112 : Nat := 201639516961776755527379

theorem tailTrace_1767112 : CollatzResearch.WordTrace tailWord_1767112 prefixEnd_1767112 201639516961776755527379 := by
  unfold tailWord_1767112
  simp only [CollatzResearch.WordTrace]
  refine ⟨32225934787031248773643795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42967913049374998364858393 32225934787031248773643795)
  ·
    refine ⟨48338902180546873160465693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32225934787031248773643795 48338902180546873160465693)
    ·
      refine ⟨18127088317705077435174635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48338902180546873160465693 18127088317705077435174635)
      ·
        refine ⟨27190632476557616152761953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18127088317705077435174635 27190632476557616152761953)
        ·
          refine ⟨20392974357418212114571465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27190632476557616152761953 20392974357418212114571465)
          ·
            refine ⟨15294730768063659085928599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20392974357418212114571465 15294730768063659085928599)
            ·
              refine ⟨22942096152095488628892899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15294730768063659085928599 22942096152095488628892899)
              ·
                refine ⟨34413144228143232943339349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22942096152095488628892899 34413144228143232943339349)
                ·
                  refine ⟨201639516961776755527379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 34413144228143232943339349 201639516961776755527379)
                  ·
                    rfl

theorem cell22_1767112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 9].length) (baseStart_1767112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1767112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1767112 prefixEnd_1767112 := by exact prefixLift 1767112
  have htrace : WordTrace (prefixWord ++ tailWord_1767112) baseStart_1767112 baseEnd_1767112 := by
    simpa [prefixWord, tailWord_1767112, baseEnd_1767112] using wordTrace_append hprefix tailTrace_1767112
  have hstable : (prefixWord ++ tailWord_1767112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767112).length < 2 ^ (prefixWord ++ tailWord_1767112).sum := by decide
  have hdescent : baseEnd_1767112 < baseStart_1767112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767146 : List Nat := [3, 1, 3, 1, 1, 1, 6, 1, 5]
def baseStart_1767146 : Nat := 118140960795 + 1767146 * 2 ^ 59
def prefixEnd_1767146 : Nat := 4983230072969 + 3 ^ 40 * 1767146 * 2
def baseEnd_1767146 : Nat := 201643396593388503744011

theorem tailTrace_1767146 : CollatzResearch.WordTrace tailWord_1767146 prefixEnd_1767146 201643396593388503744011 := by
  unfold tailWord_1767146
  simp only [CollatzResearch.WordTrace]
  refine ⟨16113277413984830338506323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42968739770626214236016861 16113277413984830338506323)
  ·
    refine ⟨24169916120977245507759485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16113277413984830338506323 24169916120977245507759485)
    ·
      refine ⟨9063718545366467065409807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24169916120977245507759485 9063718545366467065409807)
      ·
        refine ⟨13595577818049700598114711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9063718545366467065409807 13595577818049700598114711)
        ·
          refine ⟨20393366727074550897172067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13595577818049700598114711 20393366727074550897172067)
          ·
            refine ⟨30590050090611826345758101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20393366727074550897172067 30590050090611826345758101)
            ·
              refine ⟨1433908597997429359957411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30590050090611826345758101 1433908597997429359957411)
              ·
                refine ⟨2150862896996144039936117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1433908597997429359957411 2150862896996144039936117)
                ·
                  refine ⟨201643396593388503744011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2150862896996144039936117 201643396593388503744011)
                  ·
                    rfl

theorem cell22_1767146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 1, 5].length) (baseStart_1767146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1767146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1767146 prefixEnd_1767146 := by exact prefixLift 1767146
  have htrace : WordTrace (prefixWord ++ tailWord_1767146) baseStart_1767146 baseEnd_1767146 := by
    simpa [prefixWord, tailWord_1767146, baseEnd_1767146] using wordTrace_append hprefix tailTrace_1767146
  have hstable : (prefixWord ++ tailWord_1767146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767146).length < 2 ^ (prefixWord ++ tailWord_1767146).sum := by decide
  have hdescent : baseEnd_1767146 < baseStart_1767146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767221 : List Nat := [1, 3, 3, 1, 4, 1, 1, 1, 1, 6]
def baseStart_1767221 : Nat := 118140960795 + 1767221 * 2 ^ 59
def prefixEnd_1767221 : Nat := 4983230072969 + 3 ^ 40 * 1767221 * 2
def baseEnd_1767221 : Nat := 604955863812890315606803

theorem tailTrace_1767221 : CollatzResearch.WordTrace tailWord_1767221 prefixEnd_1767221 604955863812890315606803 := by
  unfold tailWord_1767221
  simp only [CollatzResearch.WordTrace]
  refine ⟨64455845130667609163005517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42970563420445072775337011 64455845130667609163005517)
  ·
    refine ⟨24170941924000353436127069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64455845130667609163005517 24170941924000353436127069)
    ·
      refine ⟨9064103221500132538547651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24170941924000353436127069 9064103221500132538547651)
      ·
        refine ⟨13596154832250198807821477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9064103221500132538547651 13596154832250198807821477)
        ·
          refine ⟨2549279031046912276466527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13596154832250198807821477 2549279031046912276466527)
          ·
            refine ⟨3823918546570368414699791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2549279031046912276466527 3823918546570368414699791)
            ·
              refine ⟨5735877819855552622049687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3823918546570368414699791 5735877819855552622049687)
              ·
                refine ⟨8603816729783328933074531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5735877819855552622049687 8603816729783328933074531)
                ·
                  refine ⟨12905725094674993399611797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8603816729783328933074531 12905725094674993399611797)
                  ·
                    refine ⟨604955863812890315606803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12905725094674993399611797 604955863812890315606803)
                    ·
                      rfl

theorem cell22_1767221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_1767221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1767221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1767221 prefixEnd_1767221 := by exact prefixLift 1767221
  have htrace : WordTrace (prefixWord ++ tailWord_1767221) baseStart_1767221 baseEnd_1767221 := by
    simpa [prefixWord, tailWord_1767221, baseEnd_1767221] using wordTrace_append hprefix tailTrace_1767221
  have hstable : (prefixWord ++ tailWord_1767221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767221).length < 2 ^ (prefixWord ++ tailWord_1767221).sum := by decide
  have hdescent : baseEnd_1767221 < baseStart_1767221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767225 : List Nat := [1, 2, 1, 7, 1, 1, 2, 3, 4]
def baseStart_1767225 : Nat := 118140960795 + 1767225 * 2 ^ 59
def prefixEnd_1767225 : Nat := 4983230072969 + 3 ^ 40 * 1767225 * 2
def baseEnd_1767225 : Nat := 201652411031545212835597

theorem tailTrace_1767225 : CollatzResearch.WordTrace tailWord_1767225 prefixEnd_1767225 201652411031545212835597 := by
  unfold tailWord_1767225
  simp only [CollatzResearch.WordTrace]
  refine ⟨64455991022653117846151129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42970660681768745230767419 64455991022653117846151129)
  ·
    refine ⟨48341993266989838384613347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64455991022653117846151129 48341993266989838384613347)
    ·
      refine ⟨72512989900484757576920021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48341993266989838384613347 72512989900484757576920021)
      ·
        refine ⟨1699523200792611505709063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 72512989900484757576920021 1699523200792611505709063)
        ·
          refine ⟨2549284801188917258563595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1699523200792611505709063 2549284801188917258563595)
          ·
            refine ⟨3823927201783375887845393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2549284801188917258563595 3823927201783375887845393)
            ·
              refine ⟨2867945401337531915884045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3823927201783375887845393 2867945401337531915884045)
              ·
                refine ⟨1075479525501574468456517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2867945401337531915884045 1075479525501574468456517)
                ·
                  refine ⟨201652411031545212835597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1075479525501574468456517 201652411031545212835597)
                  ·
                    rfl

theorem cell22_1767225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 3, 4].length) (baseStart_1767225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1767225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1767225 prefixEnd_1767225 := by exact prefixLift 1767225
  have htrace : WordTrace (prefixWord ++ tailWord_1767225) baseStart_1767225 baseEnd_1767225 := by
    simpa [prefixWord, tailWord_1767225, baseEnd_1767225] using wordTrace_append hprefix tailTrace_1767225
  have hstable : (prefixWord ++ tailWord_1767225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767225).length < 2 ^ (prefixWord ++ tailWord_1767225).sum := by decide
  have hdescent : baseEnd_1767225 < baseStart_1767225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767345 : List Nat := [1, 2, 2, 4, 2, 2, 3, 1, 1, 4]
def baseStart_1767345 : Nat := 118140960795 + 1767345 * 2 ^ 59
def prefixEnd_1767345 : Nat := 4983230072969 + 3 ^ 40 * 1767345 * 2
def baseEnd_1767345 : Nat := 604998311546995325506423

theorem tailTrace_1767345 : CollatzResearch.WordTrace tailWord_1767345 prefixEnd_1767345 604998311546995325506423 := by
  unfold tailWord_1767345
  simp only [CollatzResearch.WordTrace]
  refine ⟨64460367782218378340519489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42973578521478918893679659 64460367782218378340519489)
  ·
    refine ⟨48345275836663783755389617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64460367782218378340519489 48345275836663783755389617)
    ·
      refine ⟨36258956877497837816542213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48345275836663783755389617 36258956877497837816542213)
      ·
        refine ⟨6798554414530844590601665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36258956877497837816542213 6798554414530844590601665)
        ·
          refine ⟨5098915810898133442951249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6798554414530844590601665 5098915810898133442951249)
          ·
            refine ⟨3824186858173600082213437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5098915810898133442951249 3824186858173600082213437)
            ·
              refine ⟨1434070071815100030830039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3824186858173600082213437 1434070071815100030830039)
              ·
                refine ⟨2151105107722650046245059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1434070071815100030830039 2151105107722650046245059)
                ·
                  refine ⟨3226657661583975069367589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2151105107722650046245059 3226657661583975069367589)
                  ·
                    refine ⟨604998311546995325506423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3226657661583975069367589 604998311546995325506423)
                    ·
                      rfl

theorem cell22_1767345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 1, 1, 4].length) (baseStart_1767345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1767345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1767345 prefixEnd_1767345 := by exact prefixLift 1767345
  have htrace : WordTrace (prefixWord ++ tailWord_1767345) baseStart_1767345 baseEnd_1767345 := by
    simpa [prefixWord, tailWord_1767345, baseEnd_1767345] using wordTrace_append hprefix tailTrace_1767345
  have hstable : (prefixWord ++ tailWord_1767345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767345).length < 2 ^ (prefixWord ++ tailWord_1767345).sum := by decide
  have hdescent : baseEnd_1767345 < baseStart_1767345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767420 : List Nat := [2, 2, 2, 1, 2, 2, 1, 6, 1, 3]
def baseStart_1767420 : Nat := 118140960795 + 1767420 * 2 ^ 59
def prefixEnd_1767420 : Nat := 4983230072969 + 3 ^ 40 * 1767420 * 2
def baseEnd_1767420 : Nat := 605023985579720129881193

theorem tailTrace_1767420 : CollatzResearch.WordTrace tailWord_1767420 prefixEnd_1767420 605023985579720129881193 := by
  unfold tailWord_1767420
  simp only [CollatzResearch.WordTrace]
  refine ⟨32231551628473333074749857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42975402171297777432999809 32231551628473333074749857)
  ·
    refine ⟨24173663721354999806062393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32231551628473333074749857 24173663721354999806062393)
    ·
      refine ⟨18130247791016249854546795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24173663721354999806062393 18130247791016249854546795)
      ·
        refine ⟨27195371686524374781820193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18130247791016249854546795 27195371686524374781820193)
        ·
          refine ⟨20396528764893281086365145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27195371686524374781820193 20396528764893281086365145)
          ·
            refine ⟨15297396573669960814773859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20396528764893281086365145 15297396573669960814773859)
            ·
              refine ⟨22946094860504941222160789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15297396573669960814773859 22946094860504941222160789)
              ·
                refine ⟨1075598196586169119788787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22946094860504941222160789 1075598196586169119788787)
                ·
                  refine ⟨1613397294879253679683181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1075598196586169119788787 1613397294879253679683181)
                  ·
                    refine ⟨605023985579720129881193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1613397294879253679683181 605023985579720129881193)
                    ·
                      rfl

theorem cell22_1767420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 6, 1, 3].length) (baseStart_1767420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1767420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1767420 prefixEnd_1767420 := by exact prefixLift 1767420
  have htrace : WordTrace (prefixWord ++ tailWord_1767420) baseStart_1767420 baseEnd_1767420 := by
    simpa [prefixWord, tailWord_1767420, baseEnd_1767420] using wordTrace_append hprefix tailTrace_1767420
  have hstable : (prefixWord ++ tailWord_1767420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767420).length < 2 ^ (prefixWord ++ tailWord_1767420).sum := by decide
  have hdescent : baseEnd_1767420 < baseStart_1767420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767491 : List Nat := [1, 1, 1, 3, 1, 2, 2, 4, 1, 6]
def baseStart_1767491 : Nat := 118140960795 + 1767491 * 2 ^ 59
def prefixEnd_1767491 : Nat := 4983230072969 + 3 ^ 40 * 1767491 * 2
def baseEnd_1767491 : Nat := 605048290330699611355975

theorem tailTrace_1767491 : CollatzResearch.WordTrace tailWord_1767491 prefixEnd_1767491 605048290330699611355975 := by
  unfold tailWord_1767491
  simp only [CollatzResearch.WordTrace]
  refine ⟨64465692839689445275334327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42977128559792963516889551 64465692839689445275334327)
  ·
    refine ⟨96698539259534167913001491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64465692839689445275334327 96698539259534167913001491)
    ·
      refine ⟨145047808889301251869502237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96698539259534167913001491 145047808889301251869502237)
      ·
        refine ⟨54392928333487969451063339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145047808889301251869502237 54392928333487969451063339)
        ·
          refine ⟨81589392500231954176595009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54392928333487969451063339 81589392500231954176595009)
          ·
            refine ⟨61192044375173965632446257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81589392500231954176595009 61192044375173965632446257)
            ·
              refine ⟨45894033281380474224334693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61192044375173965632446257 45894033281380474224334693)
              ·
                refine ⟨8605131240258838917062755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45894033281380474224334693 8605131240258838917062755)
                ·
                  refine ⟨12907696860388258375594133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8605131240258838917062755 12907696860388258375594133)
                  ·
                    refine ⟨605048290330699611355975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12907696860388258375594133 605048290330699611355975)
                    ·
                      rfl

theorem cell22_1767491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 6].length) (baseStart_1767491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1767491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1767491 prefixEnd_1767491 := by exact prefixLift 1767491
  have htrace : WordTrace (prefixWord ++ tailWord_1767491) baseStart_1767491 baseEnd_1767491 := by
    simpa [prefixWord, tailWord_1767491, baseEnd_1767491] using wordTrace_append hprefix tailTrace_1767491
  have hstable : (prefixWord ++ tailWord_1767491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767491).length < 2 ^ (prefixWord ++ tailWord_1767491).sum := by decide
  have hdescent : baseEnd_1767491 < baseStart_1767491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767555 : List Nat := [1, 1, 1, 3, 3, 4, 1, 2, 3, 3]
def baseStart_1767555 : Nat := 118140960795 + 1767555 * 2 ^ 59
def prefixEnd_1767555 : Nat := 4983230072969 + 3 ^ 40 * 1767555 * 2
def baseEnd_1767555 : Nat := 605070198838624777755779

theorem tailTrace_1767555 : CollatzResearch.WordTrace tailWord_1767555 prefixEnd_1767555 605070198838624777755779 := by
  unfold tailWord_1767555
  simp only [CollatzResearch.WordTrace]
  refine ⟨64468027111457584205664119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42978684740971722803776079 64468027111457584205664119)
  ·
    refine ⟨96702040667186376308496179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64468027111457584205664119 96702040667186376308496179)
    ·
      refine ⟨145053061000779564462744269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96702040667186376308496179 145053061000779564462744269)
      ·
        refine ⟨54394897875292336673529101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145053061000779564462744269 54394897875292336673529101)
        ·
          refine ⟨20398086703234626252573413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54394897875292336673529101 20398086703234626252573413)
          ·
            refine ⟨3824641256856492422357515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20398086703234626252573413 3824641256856492422357515)
            ·
              refine ⟨5736961885284738633536273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3824641256856492422357515 5736961885284738633536273)
              ·
                refine ⟨4302721413963553975152205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5736961885284738633536273 4302721413963553975152205)
                ·
                  refine ⟨1613520530236332740682077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4302721413963553975152205 1613520530236332740682077)
                  ·
                    refine ⟨605070198838624777755779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1613520530236332740682077 605070198838624777755779)
                    ·
                      rfl

theorem cell22_1767555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 2, 3, 3].length) (baseStart_1767555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1767555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1767555 prefixEnd_1767555 := by exact prefixLift 1767555
  have htrace : WordTrace (prefixWord ++ tailWord_1767555) baseStart_1767555 baseEnd_1767555 := by
    simpa [prefixWord, tailWord_1767555, baseEnd_1767555] using wordTrace_append hprefix tailTrace_1767555
  have hstable : (prefixWord ++ tailWord_1767555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767555).length < 2 ^ (prefixWord ++ tailWord_1767555).sum := by decide
  have hdescent : baseEnd_1767555 < baseStart_1767555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767585 : List Nat := [1, 2, 3, 3, 1, 2, 3, 2, 5]
def baseStart_1767585 : Nat := 118140960795 + 1767585 * 2 ^ 59
def prefixEnd_1767585 : Nat := 4983230072969 + 3 ^ 40 * 1767585 * 2
def baseEnd_1767585 : Nat := 201693489483904899835229

theorem tailTrace_1767585 : CollatzResearch.WordTrace tailWord_1767585 prefixEnd_1767585 201693489483904899835229 := by
  unfold tailWord_1767585
  simp only [CollatzResearch.WordTrace]
  refine ⟨64469121301348899329256209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42979414200899266219504139 64469121301348899329256209)
  ·
    refine ⟨48351840976011674496942157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64469121301348899329256209 48351840976011674496942157)
    ·
      refine ⟨18131940366004377936353309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48351840976011674496942157 18131940366004377936353309)
      ·
        refine ⟨6799477637251641726132491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18131940366004377936353309 6799477637251641726132491)
        ·
          refine ⟨10199216455877462589198737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6799477637251641726132491 10199216455877462589198737)
          ·
            refine ⟨7649412341908096941899053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10199216455877462589198737 7649412341908096941899053)
            ·
              refine ⟨2868529628215536353212145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7649412341908096941899053 2868529628215536353212145)
              ·
                refine ⟨2151397221161652264909109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2868529628215536353212145 2151397221161652264909109)
                ·
                  refine ⟨201693489483904899835229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2151397221161652264909109 201693489483904899835229)
                  ·
                    rfl

theorem cell22_1767585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 2, 5].length) (baseStart_1767585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1767585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1767585 prefixEnd_1767585 := by exact prefixLift 1767585
  have htrace : WordTrace (prefixWord ++ tailWord_1767585) baseStart_1767585 baseEnd_1767585 := by
    simpa [prefixWord, tailWord_1767585, baseEnd_1767585] using wordTrace_append hprefix tailTrace_1767585
  have hstable : (prefixWord ++ tailWord_1767585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767585).length < 2 ^ (prefixWord ++ tailWord_1767585).sum := by decide
  have hdescent : baseEnd_1767585 < baseStart_1767585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767643 : List Nat := [1, 1, 1, 1, 1, 1, 1, 7, 4, 4]
def baseStart_1767643 : Nat := 118140960795 + 1767643 * 2 ^ 59
def prefixEnd_1767643 : Nat := 4983230072969 + 3 ^ 40 * 1767643 * 2
def baseEnd_1767643 : Nat := 605100323037021881555509

theorem tailTrace_1767643 : CollatzResearch.WordTrace tailWord_1767643 prefixEnd_1767643 605100323037021881555509 := by
  unfold tailWord_1767643
  simp only [CollatzResearch.WordTrace]
  refine ⟨64471236735138775234867583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42980824490092516823245055 64471236735138775234867583)
  ·
    refine ⟨96706855102708162852301375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64471236735138775234867583 96706855102708162852301375)
    ·
      refine ⟨145060282654062244278452063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96706855102708162852301375 145060282654062244278452063)
      ·
        refine ⟨217590423981093366417678095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145060282654062244278452063 217590423981093366417678095)
        ·
          refine ⟨326385635971640049626517143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217590423981093366417678095 326385635971640049626517143)
          ·
            refine ⟨489578453957460074439775715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326385635971640049626517143 489578453957460074439775715)
            ·
              refine ⟨734367680936190111659663573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 489578453957460074439775715 734367680936190111659663573)
              ·
                refine ⟨17211742521941955742023365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 734367680936190111659663573 17211742521941955742023365)
                ·
                  refine ⟨3227201722864116701629381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17211742521941955742023365 3227201722864116701629381)
                  ·
                    refine ⟨605100323037021881555509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3227201722864116701629381 605100323037021881555509)
                    ·
                      rfl

theorem cell22_1767643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 4, 4].length) (baseStart_1767643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1767643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1767643 prefixEnd_1767643 := by exact prefixLift 1767643
  have htrace : WordTrace (prefixWord ++ tailWord_1767643) baseStart_1767643 baseEnd_1767643 := by
    simpa [prefixWord, tailWord_1767643, baseEnd_1767643] using wordTrace_append hprefix tailTrace_1767643
  have hstable : (prefixWord ++ tailWord_1767643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767643).length < 2 ^ (prefixWord ++ tailWord_1767643).sum := by decide
  have hdescent : baseEnd_1767643 < baseStart_1767643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767709 : List Nat := [1, 4, 2, 3, 3, 1, 1, 7]
def baseStart_1767709 : Nat := 118140960795 + 1767709 * 2 ^ 59
def prefixEnd_1767709 : Nat := 4983230072969 + 3 ^ 40 * 1767709 * 2
def baseEnd_1767709 : Nat := 67235879576202189933923

theorem tailTrace_1767709 : CollatzResearch.WordTrace tailWord_1767709 prefixEnd_1767709 67235879576202189933923 := by
  unfold tailWord_1767709
  simp only [CollatzResearch.WordTrace]
  refine ⟨64473643952899668506770181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42982429301933112337846787 64473643952899668506770181)
  ·
    refine ⟨12088808241168687845019409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64473643952899668506770181 12088808241168687845019409)
    ·
      refine ⟨9066606180876515883764557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12088808241168687845019409 9066606180876515883764557)
      ·
        refine ⟨3399977317828693456411709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9066606180876515883764557 3399977317828693456411709)
        ·
          refine ⟨1274991494185760046154391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3399977317828693456411709 1274991494185760046154391)
          ·
            refine ⟨1912487241278640069231587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1274991494185760046154391 1912487241278640069231587)
            ·
              refine ⟨2868730861917960103847381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1912487241278640069231587 2868730861917960103847381)
              ·
                refine ⟨67235879576202189933923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2868730861917960103847381 67235879576202189933923)
                ·
                  rfl

theorem cell22_1767709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 7].length) (baseStart_1767709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1767709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1767709 prefixEnd_1767709 := by exact prefixLift 1767709
  have htrace : WordTrace (prefixWord ++ tailWord_1767709) baseStart_1767709 baseEnd_1767709 := by
    simpa [prefixWord, tailWord_1767709, baseEnd_1767709] using wordTrace_append hprefix tailTrace_1767709
  have hstable : (prefixWord ++ tailWord_1767709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767709).length < 2 ^ (prefixWord ++ tailWord_1767709).sum := by decide
  have hdescent : baseEnd_1767709 < baseStart_1767709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767784 : List Nat := [2, 1, 4, 2, 2, 2, 2, 2, 1, 4]
def baseStart_1767784 : Nat := 118140960795 + 1767784 * 2 ^ 59
def prefixEnd_1767784 : Nat := 4983230072969 + 3 ^ 40 * 1767784 * 2
def baseEnd_1767784 : Nat := 605148590218544513780077

theorem tailTrace_1767784 : CollatzResearch.WordTrace tailWord_1767784 prefixEnd_1767784 605148590218544513780077 := by
  unfold tailWord_1767784
  simp only [CollatzResearch.WordTrace]
  refine ⟨32238189713813978157875203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42984252951751970877166937 32238189713813978157875203)
  ·
    refine ⟨48357284570720967236812805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32238189713813978157875203 48357284570720967236812805)
    ·
      refine ⟨9066990857010181356902401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48357284570720967236812805 9066990857010181356902401)
      ·
        refine ⟨6800243142757636017676801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9066990857010181356902401 6800243142757636017676801)
        ·
          refine ⟨5100182357068227013257601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6800243142757636017676801 5100182357068227013257601)
          ·
            refine ⟨3825136767801170259943201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5100182357068227013257601 3825136767801170259943201)
            ·
              refine ⟨2868852575850877694957401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3825136767801170259943201 2868852575850877694957401)
              ·
                refine ⟨2151639431888158271218051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2868852575850877694957401 2151639431888158271218051)
                ·
                  refine ⟨3227459147832237406827077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2151639431888158271218051 3227459147832237406827077)
                  ·
                    refine ⟨605148590218544513780077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3227459147832237406827077 605148590218544513780077)
                    ·
                      rfl

theorem cell22_1767784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_1767784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1767784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1767784 prefixEnd_1767784 := by exact prefixLift 1767784
  have htrace : WordTrace (prefixWord ++ tailWord_1767784) baseStart_1767784 baseEnd_1767784 := by
    simpa [prefixWord, tailWord_1767784, baseEnd_1767784] using wordTrace_append hprefix tailTrace_1767784
  have hstable : (prefixWord ++ tailWord_1767784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767784).length < 2 ^ (prefixWord ++ tailWord_1767784).sum := by decide
  have hdescent : baseEnd_1767784 < baseStart_1767784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767812 : List Nat := [2, 3, 2, 1, 1, 2, 3, 2, 2, 4]
def baseStart_1767812 : Nat := 118140960795 + 1767812 * 2 ^ 59
def prefixEnd_1767812 : Nat := 4983230072969 + 3 ^ 40 * 1767812 * 2
def baseEnd_1767812 : Nat := 605158175190761774079991

theorem tailTrace_1767812 : CollatzResearch.WordTrace tailWord_1767812 prefixEnd_1767812 605158175190761774079991 := by
  unfold tailWord_1767812
  simp only [CollatzResearch.WordTrace]
  refine ⟨32238700335763258548884845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42984933781017678065179793 32238700335763258548884845)
  ·
    refine ⟨12089512625911221955831817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32238700335763258548884845 12089512625911221955831817)
    ·
      refine ⟨9067134469433416466873863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12089512625911221955831817 9067134469433416466873863)
      ·
        refine ⟨13600701704150124700310795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9067134469433416466873863 13600701704150124700310795)
        ·
          refine ⟨20401052556225187050466193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13600701704150124700310795 20401052556225187050466193)
          ·
            refine ⟨15300789417168890287849645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20401052556225187050466193 15300789417168890287849645)
            ·
              refine ⟨5737796031438333857943617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15300789417168890287849645 5737796031438333857943617)
              ·
                refine ⟨4303347023578750393457713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5737796031438333857943617 4303347023578750393457713)
                ·
                  refine ⟨3227510267684062795093285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4303347023578750393457713 3227510267684062795093285)
                  ·
                    refine ⟨605158175190761774079991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3227510267684062795093285 605158175190761774079991)
                    ·
                      rfl

theorem cell22_1767812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_1767812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1767812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1767812 prefixEnd_1767812 := by exact prefixLift 1767812
  have htrace : WordTrace (prefixWord ++ tailWord_1767812) baseStart_1767812 baseEnd_1767812 := by
    simpa [prefixWord, tailWord_1767812, baseEnd_1767812] using wordTrace_append hprefix tailTrace_1767812
  have hstable : (prefixWord ++ tailWord_1767812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767812).length < 2 ^ (prefixWord ++ tailWord_1767812).sum := by decide
  have hdescent : baseEnd_1767812 < baseStart_1767812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767947 : List Nat := [1, 1, 1, 1, 7, 1, 1, 2, 1, 6]
def baseStart_1767947 : Nat := 118140960795 + 1767947 * 2 ^ 59
def prefixEnd_1767947 : Nat := 4983230072969 + 3 ^ 40 * 1767947 * 2
def baseEnd_1767947 : Nat := 605204388449666421954577

theorem tailTrace_1767947 : CollatzResearch.WordTrace tailWord_1767947 prefixEnd_1767947 605204388449666421954577 := by
  unfold tailWord_1767947
  simp only [CollatzResearch.WordTrace]
  refine ⟨64482324526037435153934095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42988216350691623435956063 64482324526037435153934095)
  ·
    refine ⟨96723486789056152730901143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64482324526037435153934095 96723486789056152730901143)
    ·
      refine ⟨145085230183584229096351715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96723486789056152730901143 145085230183584229096351715)
      ·
        refine ⟨217627845275376343644527573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145085230183584229096351715 217627845275376343644527573)
        ·
          refine ⟨5100652623641633054168615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 217627845275376343644527573 5100652623641633054168615)
          ·
            refine ⟨7650978935462449581252923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5100652623641633054168615 7650978935462449581252923)
            ·
              refine ⟨11476468403193674371879385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7650978935462449581252923 11476468403193674371879385)
              ·
                refine ⟨8607351302395255778909539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11476468403193674371879385 8607351302395255778909539)
                ·
                  refine ⟨12911026953592883668364309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8607351302395255778909539 12911026953592883668364309)
                  ·
                    refine ⟨605204388449666421954577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12911026953592883668364309 605204388449666421954577)
                    ·
                      rfl

theorem cell22_1767947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 6].length) (baseStart_1767947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1767947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1767947 prefixEnd_1767947 := by exact prefixLift 1767947
  have htrace : WordTrace (prefixWord ++ tailWord_1767947) baseStart_1767947 baseEnd_1767947 := by
    simpa [prefixWord, tailWord_1767947, baseEnd_1767947] using wordTrace_append hprefix tailTrace_1767947
  have hstable : (prefixWord ++ tailWord_1767947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767947).length < 2 ^ (prefixWord ++ tailWord_1767947).sum := by decide
  have hdescent : baseEnd_1767947 < baseStart_1767947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767968 : List Nat := [2, 1, 1, 6, 2, 2, 1, 3, 4]
def baseStart_1767968 : Nat := 118140960795 + 1767968 * 2 ^ 59
def prefixEnd_1767968 : Nat := 4983230072969 + 3 ^ 40 * 1767968 * 2
def baseEnd_1767968 : Nat := 201737192392943122393171

theorem tailTrace_1767968 : CollatzResearch.WordTrace tailWord_1767968 prefixEnd_1767968 201737192392943122393171 := by
  unfold tailWord_1767968
  simp only [CollatzResearch.WordTrace]
  refine ⟨32241545229480677870224279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42988726972640903826965705 32241545229480677870224279)
  ·
    refine ⟨48362317844221016805336419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32241545229480677870224279 48362317844221016805336419)
    ·
      refine ⟨72543476766331525208004629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48362317844221016805336419 72543476766331525208004629)
      ·
        refine ⟨3400475473421790244125217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 72543476766331525208004629 3400475473421790244125217)
        ·
          refine ⟨2550356605066342683093913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3400475473421790244125217 2550356605066342683093913)
          ·
            refine ⟨1912767453799757012320435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2550356605066342683093913 1912767453799757012320435)
            ·
              refine ⟨2869151180699635518480653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1912767453799757012320435 2869151180699635518480653)
              ·
                refine ⟨1075931692762363319430245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2869151180699635518480653 1075931692762363319430245)
                ·
                  refine ⟨201737192392943122393171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1075931692762363319430245 201737192392943122393171)
                  ·
                    rfl

theorem cell22_1767968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 3, 4].length) (baseStart_1767968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1767968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1767968 prefixEnd_1767968 := by exact prefixLift 1767968
  have htrace : WordTrace (prefixWord ++ tailWord_1767968) baseStart_1767968 baseEnd_1767968 := by
    simpa [prefixWord, tailWord_1767968, baseEnd_1767968] using wordTrace_append hprefix tailTrace_1767968
  have hstable : (prefixWord ++ tailWord_1767968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767968).length < 2 ^ (prefixWord ++ tailWord_1767968).sum := by decide
  have hdescent : baseEnd_1767968 < baseStart_1767968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767992 : List Nat := [2, 1, 2, 1, 4, 1, 2, 1, 2, 6]
def baseStart_1767992 : Nat := 118140960795 + 1767992 * 2 ^ 59
def prefixEnd_1767992 : Nat := 4983230072969 + 3 ^ 40 * 1767992 * 2
def baseEnd_1767992 : Nat := 605219792869301304579439

theorem tailTrace_1767992 : CollatzResearch.WordTrace tailWord_1767992 prefixEnd_1767992 605219792869301304579439 := by
  unfold tailWord_1767992
  simp only [CollatzResearch.WordTrace]
  refine ⟨32241982905437203919661115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42989310540582938559548153 32241982905437203919661115)
  ·
    refine ⟨48362974358155805879491673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32241982905437203919661115 48362974358155805879491673)
    ·
      refine ⟨36272230768616854409618755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48362974358155805879491673 36272230768616854409618755)
      ·
        refine ⟨54408346152925281614428133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36272230768616854409618755 54408346152925281614428133)
        ·
          refine ⟨10201564903673490302705275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54408346152925281614428133 10201564903673490302705275)
          ·
            refine ⟨15302347355510235454057913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10201564903673490302705275 15302347355510235454057913)
            ·
              refine ⟨11476760516632676590543435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15302347355510235454057913 11476760516632676590543435)
              ·
                refine ⟨17215140774949014885815153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11476760516632676590543435 17215140774949014885815153)
                ·
                  refine ⟨12911355581211761164361365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17215140774949014885815153 12911355581211761164361365)
                  ·
                    refine ⟨605219792869301304579439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12911355581211761164361365 605219792869301304579439)
                    ·
                      rfl

theorem cell22_1767992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 2, 6].length) (baseStart_1767992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1767992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1767992 prefixEnd_1767992 := by exact prefixLift 1767992
  have htrace : WordTrace (prefixWord ++ tailWord_1767992) baseStart_1767992 baseEnd_1767992 := by
    simpa [prefixWord, tailWord_1767992, baseEnd_1767992] using wordTrace_append hprefix tailTrace_1767992
  have hstable : (prefixWord ++ tailWord_1767992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767992).length < 2 ^ (prefixWord ++ tailWord_1767992).sum := by decide
  have hdescent : baseEnd_1767992 < baseStart_1767992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768045 : List Nat := [1, 5, 1, 1, 3, 1, 4, 2, 1, 3]
def baseStart_1768045 : Nat := 118140960795 + 1768045 * 2 ^ 59
def prefixEnd_1768045 : Nat := 4983230072969 + 3 ^ 40 * 1768045 * 2
def baseEnd_1768045 : Nat := 605237935852426833004277

theorem tailTrace_1768045 : CollatzResearch.WordTrace tailWord_1768045 prefixEnd_1768045 605237935852426833004277 := by
  unfold tailWord_1768045
  simp only [CollatzResearch.WordTrace]
  refine ⟨64485898879682397891001589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42990599253121598594001059 64485898879682397891001589)
  ·
    refine ⟨6045553019970224802281399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64485898879682397891001589 6045553019970224802281399)
    ·
      refine ⟨9068329529955337203422099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6045553019970224802281399 9068329529955337203422099)
      ·
        refine ⟨13602494294933005805133149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9068329529955337203422099 13602494294933005805133149)
        ·
          refine ⟨5100935360599877176924931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13602494294933005805133149 5100935360599877176924931)
          ·
            refine ⟨7651403040899815765387397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5100935360599877176924931 7651403040899815765387397)
            ·
              refine ⟨1434638070168715456010137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7651403040899815765387397 1434638070168715456010137)
              ·
                refine ⟨1075978552626536592007603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1434638070168715456010137 1075978552626536592007603)
                ·
                  refine ⟨1613967828939804888011405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1075978552626536592007603 1613967828939804888011405)
                  ·
                    refine ⟨605237935852426833004277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1613967828939804888011405 605237935852426833004277)
                    ·
                      rfl

theorem cell22_1768045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 2, 1, 3].length) (baseStart_1768045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1768045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1768045 prefixEnd_1768045 := by exact prefixLift 1768045
  have htrace : WordTrace (prefixWord ++ tailWord_1768045) baseStart_1768045 baseEnd_1768045 := by
    simpa [prefixWord, tailWord_1768045, baseEnd_1768045] using wordTrace_append hprefix tailTrace_1768045
  have hstable : (prefixWord ++ tailWord_1768045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768045).length < 2 ^ (prefixWord ++ tailWord_1768045).sum := by decide
  have hdescent : baseEnd_1768045 < baseStart_1768045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768069 : List Nat := [1, 3, 1, 1, 4, 3, 1, 2, 6]
def baseStart_1768069 : Nat := 118140960795 + 1768069 * 2 ^ 59
def prefixEnd_1768069 : Nat := 4983230072969 + 3 ^ 40 * 1768069 * 2
def baseEnd_1768069 : Nat := 201748717180966256801401

theorem tailTrace_1768069 : CollatzResearch.WordTrace tailWord_1768069 prefixEnd_1768069 201748717180966256801401 := by
  unfold tailWord_1768069
  simp only [CollatzResearch.WordTrace]
  refine ⟨64486774231595449989875261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42991182821063633326583507 64486774231595449989875261)
  ·
    refine ⟨24182540336848293746203223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64486774231595449989875261 24182540336848293746203223)
    ·
      refine ⟨36273810505272440619304835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24182540336848293746203223 36273810505272440619304835)
      ·
        refine ⟨54410715757908660928957253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36273810505272440619304835 54410715757908660928957253)
        ·
          refine ⟨10202009204607873924179485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54410715757908660928957253 10202009204607873924179485)
          ·
            refine ⟨3825753451727952721567307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10202009204607873924179485 3825753451727952721567307)
            ·
              refine ⟨5738630177591929082350961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3825753451727952721567307 5738630177591929082350961)
              ·
                refine ⟨4303972633193946811763221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5738630177591929082350961 4303972633193946811763221)
                ·
                  refine ⟨201748717180966256801401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4303972633193946811763221 201748717180966256801401)
                  ·
                    rfl

theorem cell22_1768069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 2, 6].length) (baseStart_1768069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1768069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1768069 prefixEnd_1768069 := by exact prefixLift 1768069
  have htrace : WordTrace (prefixWord ++ tailWord_1768069) baseStart_1768069 baseEnd_1768069 := by
    simpa [prefixWord, tailWord_1768069, baseEnd_1768069] using wordTrace_append hprefix tailTrace_1768069
  have hstable : (prefixWord ++ tailWord_1768069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768069).length < 2 ^ (prefixWord ++ tailWord_1768069).sum := by decide
  have hdescent : baseEnd_1768069 < baseStart_1768069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768103 : List Nat := [1, 1, 6, 3, 1, 1, 2, 1, 6]
def baseStart_1768103 : Nat := 118140960795 + 1768103 * 2 ^ 59
def prefixEnd_1768103 : Nat := 4983230072969 + 3 ^ 40 * 1768103 * 2
def baseEnd_1768103 : Nat := 201752596812578005018033

theorem tailTrace_1768103 : CollatzResearch.WordTrace tailWord_1768103 prefixEnd_1768103 201752596812578005018033 := by
  unfold tailWord_1768103
  simp only [CollatzResearch.WordTrace]
  refine ⟨64488014313472273796612963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42992009542314849197741975 64488014313472273796612963)
  ·
    refine ⟨96732021470208410694919445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64488014313472273796612963 96732021470208410694919445)
    ·
      refine ⟨4534313506416019251324349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 96732021470208410694919445 4534313506416019251324349)
      ·
        refine ⟨1700367564906007219246631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4534313506416019251324349 1700367564906007219246631)
        ·
          refine ⟨2550551347359010828869947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1700367564906007219246631 2550551347359010828869947)
          ·
            refine ⟨3825827021038516243304921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2550551347359010828869947 3825827021038516243304921)
            ·
              refine ⟨2869370265778887182478691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3825827021038516243304921 2869370265778887182478691)
              ·
                refine ⟨4304055398668330773718037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2869370265778887182478691 4304055398668330773718037)
                ·
                  refine ⟨201752596812578005018033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4304055398668330773718037 201752596812578005018033)
                  ·
                    rfl

theorem cell22_1768103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 1, 6].length) (baseStart_1768103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1768103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1768103 prefixEnd_1768103 := by exact prefixLift 1768103
  have htrace : WordTrace (prefixWord ++ tailWord_1768103) baseStart_1768103 baseEnd_1768103 := by
    simpa [prefixWord, tailWord_1768103, baseEnd_1768103] using wordTrace_append hprefix tailTrace_1768103
  have hstable : (prefixWord ++ tailWord_1768103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768103).length < 2 ^ (prefixWord ++ tailWord_1768103).sum := by decide
  have hdescent : baseEnd_1768103 < baseStart_1768103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768148 : List Nat := [2, 4, 1, 3, 3, 1, 8]
def baseStart_1768148 : Nat := 118140960795 + 1768148 * 2 ^ 59
def prefixEnd_1768148 : Nat := 4983230072969 + 3 ^ 40 * 1768148 * 2
def baseEnd_1768148 : Nat := 22417525735458107321443

theorem tailTrace_1768148 : CollatzResearch.WordTrace tailWord_1768148 prefixEnd_1768148 22417525735458107321443 := by
  unfold tailWord_1768148
  simp only [CollatzResearch.WordTrace]
  refine ⟨32244827799154623241000549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42993103732206164321334065 32244827799154623241000549)
  ·
    refine ⟨6045905212341491857687603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32244827799154623241000549 6045905212341491857687603)
    ·
      refine ⟨9068857818512237786531405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6045905212341491857687603 9068857818512237786531405)
      ·
        refine ⟨3400821681942089169949277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9068857818512237786531405 3400821681942089169949277)
        ·
          refine ⟨1275308130728283438730979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3400821681942089169949277 1275308130728283438730979)
          ·
            refine ⟨1912962196092425158096469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1275308130728283438730979 1912962196092425158096469)
            ·
              refine ⟨22417525735458107321443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1912962196092425158096469 22417525735458107321443)
              ·
                rfl

theorem cell22_1768148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 8].length) (baseStart_1768148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1768148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1768148 prefixEnd_1768148 := by exact prefixLift 1768148
  have htrace : WordTrace (prefixWord ++ tailWord_1768148) baseStart_1768148 baseEnd_1768148 := by
    simpa [prefixWord, tailWord_1768148, baseEnd_1768148] using wordTrace_append hprefix tailTrace_1768148
  have hstable : (prefixWord ++ tailWord_1768148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768148).length < 2 ^ (prefixWord ++ tailWord_1768148).sum := by decide
  have hdescent : baseEnd_1768148 < baseStart_1768148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768159 : List Nat := [1, 1, 2, 3, 2, 3, 2, 1, 7]
def baseStart_1768159 : Nat := 118140960795 + 1768159 * 2 ^ 59
def prefixEnd_1768159 : Nat := 4983230072969 + 3 ^ 40 * 1768159 * 2
def baseEnd_1768159 : Nat := 201758986794056178551309

theorem tailTrace_1768159 : CollatzResearch.WordTrace tailWord_1768159 prefixEnd_1768159 201758986794056178551309 := by
  unfold tailWord_1768159
  simp only [CollatzResearch.WordTrace]
  refine ⟨64490056801269395360651531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42993371200846263573767687 64490056801269395360651531)
  ·
    refine ⟨96735085201904093040977297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64490056801269395360651531 96735085201904093040977297)
    ·
      refine ⟨72551313901428069780732973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96735085201904093040977297 72551313901428069780732973)
      ·
        refine ⟨27206742713035526167774865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72551313901428069780732973 27206742713035526167774865)
        ·
          refine ⟨20405057034776644625831149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27206742713035526167774865 20405057034776644625831149)
          ·
            refine ⟨7651896388041241734686681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20405057034776644625831149 7651896388041241734686681)
            ·
              refine ⟨5738922291030931301015011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7651896388041241734686681 5738922291030931301015011)
              ·
                refine ⟨8608383436546396951522517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5738922291030931301015011 8608383436546396951522517)
                ·
                  refine ⟨201758986794056178551309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8608383436546396951522517 201758986794056178551309)
                  ·
                    rfl

theorem cell22_1768159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 7].length) (baseStart_1768159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1768159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1768159 prefixEnd_1768159 := by exact prefixLift 1768159
  have htrace : WordTrace (prefixWord ++ tailWord_1768159) baseStart_1768159 baseEnd_1768159 := by
    simpa [prefixWord, tailWord_1768159, baseEnd_1768159] using wordTrace_append hprefix tailTrace_1768159
  have hstable : (prefixWord ++ tailWord_1768159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768159).length < 2 ^ (prefixWord ++ tailWord_1768159).sum := by decide
  have hdescent : baseEnd_1768159 < baseStart_1768159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768163 : List Nat := [1, 1, 1, 7, 1, 1, 3, 1, 3, 3]
def baseStart_1768163 : Nat := 118140960795 + 1768163 * 2 ^ 59
def prefixEnd_1768163 : Nat := 4983230072969 + 3 ^ 40 * 1768163 * 2
def baseEnd_1768163 : Nat := 605278329663913858553915

theorem tailTrace_1768163 : CollatzResearch.WordTrace tailWord_1768163 prefixEnd_1768163 605278329663913858553915 := by
  unfold tailWord_1768163
  simp only [CollatzResearch.WordTrace]
  refine ⟨64490202693254904043797143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42993468462169936029198095 64490202693254904043797143)
  ·
    refine ⟨96735304039882356065695715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64490202693254904043797143 96735304039882356065695715)
    ·
      refine ⟨145102956059823534098543573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96735304039882356065695715 145102956059823534098543573)
      ·
        refine ⟨3400850532652114080434615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 145102956059823534098543573 3400850532652114080434615)
        ·
          refine ⟨5101275798978171120651923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3400850532652114080434615 5101275798978171120651923)
          ·
            refine ⟨7651913698467256680977885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5101275798978171120651923 7651913698467256680977885)
            ·
              refine ⟨2869467636925221255366707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7651913698467256680977885 2869467636925221255366707)
              ·
                refine ⟨4304201455387831883050061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2869467636925221255366707 4304201455387831883050061)
                ·
                  refine ⟨1614075545770436956143773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4304201455387831883050061 1614075545770436956143773)
                  ·
                    refine ⟨605278329663913858553915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1614075545770436956143773 605278329663913858553915)
                    ·
                      rfl

theorem cell22_1768163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 1, 3, 3].length) (baseStart_1768163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1768163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1768163 prefixEnd_1768163 := by exact prefixLift 1768163
  have htrace : WordTrace (prefixWord ++ tailWord_1768163) baseStart_1768163 baseEnd_1768163 := by
    simpa [prefixWord, tailWord_1768163, baseEnd_1768163] using wordTrace_append hprefix tailTrace_1768163
  have hstable : (prefixWord ++ tailWord_1768163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768163).length < 2 ^ (prefixWord ++ tailWord_1768163).sum := by decide
  have hdescent : baseEnd_1768163 < baseStart_1768163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768210 : List Nat := [3, 2, 4, 1, 2, 1, 2, 2, 5]
def baseStart_1768210 : Nat := 118140960795 + 1768210 * 2 ^ 59
def prefixEnd_1768210 : Nat := 4983230072969 + 3 ^ 40 * 1768210 * 2
def baseEnd_1768210 : Nat := 201764806241473800876257

theorem tailTrace_1768210 : CollatzResearch.WordTrace tailWord_1768210 prefixEnd_1768210 201764806241473800876257 := by
  unfold tailWord_1768210
  simp only [CollatzResearch.WordTrace]
  refine ⟨16122979231021157767689521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42994611282723087380505389 16122979231021157767689521)
  ·
    refine ⟨12092234423265868325767141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16122979231021157767689521 12092234423265868325767141)
    ·
      refine ⟨2267293954362350311081339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12092234423265868325767141 2267293954362350311081339)
      ·
        refine ⟨3400940931543525466622009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2267293954362350311081339 3400940931543525466622009)
        ·
          refine ⟨2550705698657644099966507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3400940931543525466622009 2550705698657644099966507)
          ·
            refine ⟨3826058547986466149949761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2550705698657644099966507 3826058547986466149949761)
            ·
              refine ⟨2869543910989849612462321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3826058547986466149949761 2869543910989849612462321)
              ·
                refine ⟨2152157933242387209346741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2869543910989849612462321 2152157933242387209346741)
                ·
                  refine ⟨201764806241473800876257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2152157933242387209346741 201764806241473800876257)
                  ·
                    rfl

theorem cell22_1768210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 2, 5].length) (baseStart_1768210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1768210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1768210 prefixEnd_1768210 := by exact prefixLift 1768210
  have htrace : WordTrace (prefixWord ++ tailWord_1768210) baseStart_1768210 baseEnd_1768210 := by
    simpa [prefixWord, tailWord_1768210, baseEnd_1768210] using wordTrace_append hprefix tailTrace_1768210
  have hstable : (prefixWord ++ tailWord_1768210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768210).length < 2 ^ (prefixWord ++ tailWord_1768210).sum := by decide
  have hdescent : baseEnd_1768210 < baseStart_1768210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768236 : List Nat := [2, 2, 1, 1, 1, 4, 4, 1, 1, 5]
def baseStart_1768236 : Nat := 118140960795 + 1768236 * 2 ^ 59
def prefixEnd_1768236 : Nat := 4983230072969 + 3 ^ 40 * 1768236 * 2
def baseEnd_1768236 : Nat := 605303319055766001478691

theorem tailTrace_1768236 : CollatzResearch.WordTrace tailWord_1768236 prefixEnd_1768236 605303319055766001478691 := by
  unfold tailWord_1768236
  simp only [CollatzResearch.WordTrace]
  refine ⟨32246432610995218755602281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42995243481326958340803041 32246432610995218755602281)
  ·
    refine ⟨24184824458246414066701711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32246432610995218755602281 24184824458246414066701711)
    ·
      refine ⟨36277236687369621100052567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24184824458246414066701711 36277236687369621100052567)
      ·
        refine ⟨54415855031054431650078851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36277236687369621100052567 54415855031054431650078851)
        ·
          refine ⟨81623782546581647475118277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54415855031054431650078851 81623782546581647475118277)
          ·
            refine ⟨15304459227484058901584677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81623782546581647475118277 15304459227484058901584677)
            ·
              refine ⟨2869586105153261044047127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15304459227484058901584677 2869586105153261044047127)
              ·
                refine ⟨4304379157729891566070691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2869586105153261044047127 4304379157729891566070691)
                ·
                  refine ⟨6456568736594837349106037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4304379157729891566070691 6456568736594837349106037)
                  ·
                    refine ⟨605303319055766001478691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6456568736594837349106037 605303319055766001478691)
                    ·
                      rfl

theorem cell22_1768236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 5].length) (baseStart_1768236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1768236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1768236 prefixEnd_1768236 := by exact prefixLift 1768236
  have htrace : WordTrace (prefixWord ++ tailWord_1768236) baseStart_1768236 baseEnd_1768236 := by
    simpa [prefixWord, tailWord_1768236, baseEnd_1768236] using wordTrace_append hprefix tailTrace_1768236
  have hstable : (prefixWord ++ tailWord_1768236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768236).length < 2 ^ (prefixWord ++ tailWord_1768236).sum := by decide
  have hdescent : baseEnd_1768236 < baseStart_1768236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768238 : List Nat := [4, 1, 3, 2, 1, 2, 1, 2, 6]
def baseStart_1768238 : Nat := 118140960795 + 1768238 * 2 ^ 59
def prefixEnd_1768238 : Nat := 4983230072969 + 3 ^ 40 * 1768238 * 2
def baseEnd_1768238 : Nat := 201768001232212887642895

theorem tailTrace_1768238 : CollatzResearch.WordTrace tailWord_1768238 prefixEnd_1768238 201768001232212887642895 := by
  unfold tailWord_1768238
  simp only [CollatzResearch.WordTrace]
  refine ⟨8061617270997898981597171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42995292111988794568518245 8061617270997898981597171)
  ·
    refine ⟨12092425906496848472395757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8061617270997898981597171 12092425906496848472395757)
    ·
      refine ⟨4534659714936318177148409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12092425906496848472395757 4534659714936318177148409)
      ·
        refine ⟨3400994786202238632861307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4534659714936318177148409 3400994786202238632861307)
        ·
          refine ⟨5101492179303357949291961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3400994786202238632861307 5101492179303357949291961)
          ·
            refine ⟨3826119134477518461968971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5101492179303357949291961 3826119134477518461968971)
            ·
              refine ⟨5739178701716277692953457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3826119134477518461968971 5739178701716277692953457)
              ·
                refine ⟨4304384026287208269715093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5739178701716277692953457 4304384026287208269715093)
                ·
                  refine ⟨201768001232212887642895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4304384026287208269715093 201768001232212887642895)
                  ·
                    rfl

theorem cell22_1768238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 2, 6].length) (baseStart_1768238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1768238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1768238 prefixEnd_1768238 := by exact prefixLift 1768238
  have htrace : WordTrace (prefixWord ++ tailWord_1768238) baseStart_1768238 baseEnd_1768238 := by
    simpa [prefixWord, tailWord_1768238, baseEnd_1768238] using wordTrace_append hprefix tailTrace_1768238
  have hstable : (prefixWord ++ tailWord_1768238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768238).length < 2 ^ (prefixWord ++ tailWord_1768238).sum := by decide
  have hdescent : baseEnd_1768238 < baseStart_1768238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768315 : List Nat := [1, 1, 1, 1, 1, 5, 5, 3, 1, 3]
def baseStart_1768315 : Nat := 118140960795 + 1768315 * 2 ^ 59
def prefixEnd_1768315 : Nat := 4983230072969 + 3 ^ 40 * 1768315 * 2
def baseEnd_1768315 : Nat := 605330362370236128753449

theorem tailTrace_1768315 : CollatzResearch.WordTrace tailWord_1768315 prefixEnd_1768315 605330362370236128753449 := by
  unfold tailWord_1768315
  simp only [CollatzResearch.WordTrace]
  refine ⟨64495746588704234003330399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42997164392469489335553599 64495746588704234003330399)
  ·
    refine ⟨96743619883056351004995599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64495746588704234003330399 96743619883056351004995599)
    ·
      refine ⟨145115429824584526507493399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96743619883056351004995599 145115429824584526507493399)
      ·
        refine ⟨217673144736876789761240099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145115429824584526507493399 217673144736876789761240099)
        ·
          refine ⟨326509717105315184641860149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217673144736876789761240099 326509717105315184641860149)
          ·
            refine ⟨30610285978623298560174389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 326509717105315184641860149 30610285978623298560174389)
            ·
              refine ⟨2869714310495934240016349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30610285978623298560174389 2869714310495934240016349)
              ·
                refine ⟨1076142866435975340006131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2869714310495934240016349 1076142866435975340006131)
                ·
                  refine ⟨1614214299653963010009197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1076142866435975340006131 1614214299653963010009197)
                  ·
                    refine ⟨605330362370236128753449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1614214299653963010009197 605330362370236128753449)
                    ·
                      rfl

theorem cell22_1768315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 3, 1, 3].length) (baseStart_1768315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1768315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1768315 prefixEnd_1768315 := by exact prefixLift 1768315
  have htrace : WordTrace (prefixWord ++ tailWord_1768315) baseStart_1768315 baseEnd_1768315 := by
    simpa [prefixWord, tailWord_1768315, baseEnd_1768315] using wordTrace_append hprefix tailTrace_1768315
  have hstable : (prefixWord ++ tailWord_1768315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768315).length < 2 ^ (prefixWord ++ tailWord_1768315).sum := by decide
  have hdescent : baseEnd_1768315 < baseStart_1768315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768356 : List Nat := [2, 3, 1, 2, 1, 2, 2, 1, 8]
def baseStart_1768356 : Nat := 118140960795 + 1768356 * 2 ^ 59
def prefixEnd_1768356 : Nat := 4983230072969 + 3 ^ 40 * 1768356 * 2
def baseEnd_1768356 : Nat := 201781465836041896159441

theorem tailTrace_1768356 : CollatzResearch.WordTrace tailWord_1768356 prefixEnd_1768356 201781465836041896159441 := by
  unfold tailWord_1768356
  simp only [CollatzResearch.WordTrace]
  refine ⟨32248620990777849002786461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42998161321037132003715281 32248620990777849002786461)
  ·
    refine ⟨12093232871541693376044923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32248620990777849002786461 12093232871541693376044923)
    ·
      refine ⟨18139849307312540064067385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12093232871541693376044923 18139849307312540064067385)
      ·
        refine ⟨13604886980484405048050539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18139849307312540064067385 13604886980484405048050539)
        ·
          refine ⟨20407330470726607572075809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13604886980484405048050539 20407330470726607572075809)
          ·
            refine ⟨15305497853044955679056857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20407330470726607572075809 15305497853044955679056857)
            ·
              refine ⟨11479123389783716759292643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15305497853044955679056857 11479123389783716759292643)
              ·
                refine ⟨17218685084675575138938965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11479123389783716759292643 17218685084675575138938965)
                ·
                  refine ⟨201781465836041896159441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17218685084675575138938965 201781465836041896159441)
                  ·
                    rfl

theorem cell22_1768356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 8].length) (baseStart_1768356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1768356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1768356 prefixEnd_1768356 := by exact prefixLift 1768356
  have htrace : WordTrace (prefixWord ++ tailWord_1768356) baseStart_1768356 baseEnd_1768356 := by
    simpa [prefixWord, tailWord_1768356, baseEnd_1768356] using wordTrace_append hprefix tailTrace_1768356
  have hstable : (prefixWord ++ tailWord_1768356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768356).length < 2 ^ (prefixWord ++ tailWord_1768356).sum := by decide
  have hdescent : baseEnd_1768356 < baseStart_1768356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768405 : List Nat := [1, 3, 2, 3, 3, 1, 2, 1, 1, 5]
def baseStart_1768405 : Nat := 118140960795 + 1768405 * 2 ^ 59
def prefixEnd_1768405 : Nat := 4983230072969 + 3 ^ 40 * 1768405 * 2
def baseEnd_1768405 : Nat := 605361171209505894003173

theorem tailTrace_1768405 : CollatzResearch.WordTrace tailWord_1768405 prefixEnd_1768405 605361171209505894003173 := by
  unfold tailWord_1768405
  simp only [CollatzResearch.WordTrace]
  refine ⟨64499029158378179374106669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42999352772252119582737779 64499029158378179374106669)
  ·
    refine ⟨24187135934391817265290001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64499029158378179374106669 24187135934391817265290001)
    ·
      refine ⟨18140351950793862948967501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24187135934391817265290001 18140351950793862948967501)
      ·
        refine ⟨6802631981547698605862813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18140351950793862948967501 6802631981547698605862813)
        ·
          refine ⟨2550986993080386977198555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6802631981547698605862813 2550986993080386977198555)
          ·
            refine ⟨3826480489620580465797833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2550986993080386977198555 3826480489620580465797833)
            ·
              refine ⟨2869860367215435349348375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3826480489620580465797833 2869860367215435349348375)
              ·
                refine ⟨4304790550823153024022563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2869860367215435349348375 4304790550823153024022563)
                ·
                  refine ⟨6457185826234729536033845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4304790550823153024022563 6457185826234729536033845)
                  ·
                    refine ⟨605361171209505894003173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6457185826234729536033845 605361171209505894003173)
                    ·
                      rfl

theorem cell22_1768405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 1, 1, 5].length) (baseStart_1768405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1768405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1768405 prefixEnd_1768405 := by exact prefixLift 1768405
  have htrace : WordTrace (prefixWord ++ tailWord_1768405) baseStart_1768405 baseEnd_1768405 := by
    simpa [prefixWord, tailWord_1768405, baseEnd_1768405] using wordTrace_append hprefix tailTrace_1768405
  have hstable : (prefixWord ++ tailWord_1768405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768405).length < 2 ^ (prefixWord ++ tailWord_1768405).sum := by decide
  have hdescent : baseEnd_1768405 < baseStart_1768405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768484 : List Nat := [2, 3, 1, 4, 1, 1, 3, 3, 1, 3]
def baseStart_1768484 : Nat := 118140960795 + 1768484 * 2 ^ 59
def prefixEnd_1768484 : Nat := 4983230072969 + 3 ^ 40 * 1768484 * 2
def baseEnd_1768484 : Nat := 605388214523976021277931

theorem tailTrace_1768484 : CollatzResearch.WordTrace tailWord_1768484 prefixEnd_1768484 605388214523976021277931 := by
  unfold tailWord_1768484
  simp only [CollatzResearch.WordTrace]
  refine ⟨32250955262545987933116253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43001273683394650577488337 32250955262545987933116253)
  ·
    refine ⟨12094108223454745474918595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32250955262545987933116253 12094108223454745474918595)
    ·
      refine ⟨18141162335182118212377893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12094108223454745474918595 18141162335182118212377893)
      ·
        refine ⟨3401467937846647164820855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18141162335182118212377893 3401467937846647164820855)
        ·
          refine ⟨5102201906769970747231283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3401467937846647164820855 5102201906769970747231283)
          ·
            refine ⟨7653302860154956120846925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5102201906769970747231283 7653302860154956120846925)
            ·
              refine ⟨2869988572558108545317597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7653302860154956120846925 2869988572558108545317597)
              ·
                refine ⟨1076245714709290704494099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2869988572558108545317597 1076245714709290704494099)
                ·
                  refine ⟨1614368572063936056741149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1076245714709290704494099 1614368572063936056741149)
                  ·
                    refine ⟨605388214523976021277931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1614368572063936056741149 605388214523976021277931)
                    ·
                      rfl

theorem cell22_1768484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 3, 1, 3].length) (baseStart_1768484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1768484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1768484 prefixEnd_1768484 := by exact prefixLift 1768484
  have htrace : WordTrace (prefixWord ++ tailWord_1768484) baseStart_1768484 baseEnd_1768484 := by
    simpa [prefixWord, tailWord_1768484, baseEnd_1768484] using wordTrace_append hprefix tailTrace_1768484
  have hstable : (prefixWord ++ tailWord_1768484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768484).length < 2 ^ (prefixWord ++ tailWord_1768484).sum := by decide
  have hdescent : baseEnd_1768484 < baseStart_1768484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768540 : List Nat := [2, 2, 4, 1, 1, 1, 3, 2, 1, 5]
def baseStart_1768540 : Nat := 118140960795 + 1768540 * 2 ^ 59
def prefixEnd_1768540 : Nat := 4983230072969 + 3 ^ 40 * 1768540 * 2
def baseEnd_1768540 : Nat := 605407384468410541877759

theorem tailTrace_1768540 : CollatzResearch.WordTrace tailWord_1768540 prefixEnd_1768540 605407384468410541877759 := by
  unfold tailWord_1768540
  simp only [CollatzResearch.WordTrace]
  refine ⟨32251976506444548715135537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43002635341926064953514049 32251976506444548715135537)
  ·
    refine ⟨24188982379833411536351653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32251976506444548715135537 24188982379833411536351653)
    ·
      refine ⟨4535434196218764663065935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24188982379833411536351653 4535434196218764663065935)
      ·
        refine ⟨6803151294328146994598903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4535434196218764663065935 6803151294328146994598903)
        ·
          refine ⟨10204726941492220491898355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6803151294328146994598903 10204726941492220491898355)
          ·
            refine ⟨15307090412238330737847533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10204726941492220491898355 15307090412238330737847533)
            ·
              refine ⟨5740158904589374026692825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15307090412238330737847533 5740158904589374026692825)
              ·
                refine ⟨4305119178442030520019619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5740158904589374026692825 4305119178442030520019619)
                ·
                  refine ⟨6457678767663045780029429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4305119178442030520019619 6457678767663045780029429)
                  ·
                    refine ⟨605407384468410541877759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6457678767663045780029429 605407384468410541877759)
                    ·
                      rfl

theorem cell22_1768540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_1768540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1768540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1768540 prefixEnd_1768540 := by exact prefixLift 1768540
  have htrace : WordTrace (prefixWord ++ tailWord_1768540) baseStart_1768540 baseEnd_1768540 := by
    simpa [prefixWord, tailWord_1768540, baseEnd_1768540] using wordTrace_append hprefix tailTrace_1768540
  have hstable : (prefixWord ++ tailWord_1768540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768540).length < 2 ^ (prefixWord ++ tailWord_1768540).sum := by decide
  have hdescent : baseEnd_1768540 < baseStart_1768540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768557 : List Nat := [1, 5, 1, 1, 2, 2, 1, 4, 2, 3]
def baseStart_1768557 : Nat := 118140960795 + 1768557 * 2 ^ 59
def prefixEnd_1768557 : Nat := 4983230072969 + 3 ^ 40 * 1768557 * 2
def baseEnd_1768557 : Nat := 605413203915828164202707

theorem tailTrace_1768557 : CollatzResearch.WordTrace tailWord_1768557 prefixEnd_1768557 605413203915828164202707 := by
  unfold tailWord_1768557
  simp only [CollatzResearch.WordTrace]
  refine ⟨64504573053827509333639925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43003048702551672889093283 64504573053827509333639925)
  ·
    refine ⟨6047303723796329000028743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64504573053827509333639925 6047303723796329000028743)
    ·
      refine ⟨9070955585694493500043115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6047303723796329000028743 9070955585694493500043115)
      ·
        refine ⟨13606433378541740250064673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9070955585694493500043115 13606433378541740250064673)
        ·
          refine ⟨10204825033906305187548505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13606433378541740250064673 10204825033906305187548505)
          ·
            refine ⟨7653618775429728890661379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10204825033906305187548505 7653618775429728890661379)
            ·
              refine ⟨11480428163144593335992069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7653618775429728890661379 11480428163144593335992069)
              ·
                refine ⟨2152580280589611250498513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11480428163144593335992069 2152580280589611250498513)
                ·
                  refine ⟨1614435210442208437873885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2152580280589611250498513 1614435210442208437873885)
                  ·
                    refine ⟨605413203915828164202707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1614435210442208437873885 605413203915828164202707)
                    ·
                      rfl

theorem cell22_1768557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_1768557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1768557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1768557 prefixEnd_1768557 := by exact prefixLift 1768557
  have htrace : WordTrace (prefixWord ++ tailWord_1768557) baseStart_1768557 baseEnd_1768557 := by
    simpa [prefixWord, tailWord_1768557, baseEnd_1768557] using wordTrace_append hprefix tailTrace_1768557
  have hstable : (prefixWord ++ tailWord_1768557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768557).length < 2 ^ (prefixWord ++ tailWord_1768557).sum := by decide
  have hdescent : baseEnd_1768557 < baseStart_1768557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768583 : List Nat := [1, 1, 4, 2, 1, 1, 1, 1, 4, 6]
def baseStart_1768583 : Nat := 118140960795 + 1768583 * 2 ^ 59
def prefixEnd_1768583 : Nat := 4983230072969 + 3 ^ 40 * 1768583 * 2
def baseEnd_1768583 : Nat := 605422104247172763052627

theorem tailTrace_1768583 : CollatzResearch.WordTrace tailWord_1768583 prefixEnd_1768583 605422104247172763052627 := by
  unfold tailWord_1768583
  simp only [CollatzResearch.WordTrace]
  refine ⟨64505521351733315774086403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43003680901155543849390935 64505521351733315774086403)
  ·
    refine ⟨96758282027599973661129605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64505521351733315774086403 96758282027599973661129605)
    ·
      refine ⟨18142177880174995061461801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96758282027599973661129605 18142177880174995061461801)
      ·
        refine ⟨13606633410131246296096351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18142177880174995061461801 13606633410131246296096351)
        ·
          refine ⟨20409950115196869444144527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13606633410131246296096351 20409950115196869444144527)
          ·
            refine ⟨30614925172795304166216791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20409950115196869444144527 30614925172795304166216791)
            ·
              refine ⟨45922387759192956249325187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30614925172795304166216791 45922387759192956249325187)
              ·
                refine ⟨68883581638789434373987781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45922387759192956249325187 68883581638789434373987781)
                ·
                  refine ⟨12915671557273018945122709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68883581638789434373987781 12915671557273018945122709)
                  ·
                    refine ⟨605422104247172763052627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12915671557273018945122709 605422104247172763052627)
                    ·
                      rfl

theorem cell22_1768583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_1768583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1768583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1768583 prefixEnd_1768583 := by exact prefixLift 1768583
  have htrace : WordTrace (prefixWord ++ tailWord_1768583) baseStart_1768583 baseEnd_1768583 := by
    simpa [prefixWord, tailWord_1768583, baseEnd_1768583] using wordTrace_append hprefix tailTrace_1768583
  have hstable : (prefixWord ++ tailWord_1768583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768583).length < 2 ^ (prefixWord ++ tailWord_1768583).sum := by decide
  have hdescent : baseEnd_1768583 < baseStart_1768583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768585 : List Nat := [1, 2, 1, 1, 4, 3, 1, 1, 5, 3]
def baseStart_1768585 : Nat := 118140960795 + 1768585 * 2 ^ 59
def prefixEnd_1768585 : Nat := 4983230072969 + 3 ^ 40 * 1768585 * 2
def baseEnd_1768585 : Nat := 605422788888045424502621

theorem tailTrace_1768585 : CollatzResearch.WordTrace tailWord_1768585 prefixEnd_1768585 605422788888045424502621 := by
  unfold tailWord_1768585
  simp only [CollatzResearch.WordTrace]
  refine ⟨64505594297726070115659209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43003729531817380077106139 64505594297726070115659209)
  ·
    refine ⟨48379195723294552586744407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64505594297726070115659209 48379195723294552586744407)
    ·
      refine ⟨72568793584941828880116611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48379195723294552586744407 72568793584941828880116611)
      ·
        refine ⟨108853190377412743320174917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72568793584941828880116611 108853190377412743320174917)
        ·
          refine ⟨20409973195764889372532797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108853190377412743320174917 20409973195764889372532797)
          ·
            refine ⟨7653739948411833514699799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20409973195764889372532797 7653739948411833514699799)
            ·
              refine ⟨11480609922617750272049699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7653739948411833514699799 11480609922617750272049699)
              ·
                refine ⟨17220914883926625408074549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11480609922617750272049699 17220914883926625408074549)
                ·
                  refine ⟨1614460770368121132006989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17220914883926625408074549 1614460770368121132006989)
                  ·
                    refine ⟨605422788888045424502621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1614460770368121132006989 605422788888045424502621)
                    ·
                      rfl

theorem cell22_1768585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 5, 3].length) (baseStart_1768585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1768585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1768585 prefixEnd_1768585 := by exact prefixLift 1768585
  have htrace : WordTrace (prefixWord ++ tailWord_1768585) baseStart_1768585 baseEnd_1768585 := by
    simpa [prefixWord, tailWord_1768585, baseEnd_1768585] using wordTrace_append hprefix tailTrace_1768585
  have hstable : (prefixWord ++ tailWord_1768585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768585).length < 2 ^ (prefixWord ++ tailWord_1768585).sum := by decide
  have hdescent : baseEnd_1768585 < baseStart_1768585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768643 : List Nat := [1, 1, 1, 3, 1, 1, 1, 5, 8]
def baseStart_1768643 : Nat := 118140960795 + 1768643 * 2 ^ 59
def prefixEnd_1768643 : Nat := 4983230072969 + 3 ^ 40 * 1768643 * 2
def baseEnd_1768643 : Nat := 201814214491117535517481

theorem tailTrace_1768643 : CollatzResearch.WordTrace tailWord_1768643 prefixEnd_1768643 201814214491117535517481 := by
  unfold tailWord_1768643
  simp only [CollatzResearch.WordTrace]
  refine ⟨64507709731515946021270583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43005139821010630680847055 64507709731515946021270583)
  ·
    refine ⟨96761564597273919031905875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64507709731515946021270583 96761564597273919031905875)
    ·
      refine ⟨145142346895910878547858813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96761564597273919031905875 145142346895910878547858813)
      ·
        refine ⟨54428380085966579455447055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145142346895910878547858813 54428380085966579455447055)
        ·
          refine ⟨81642570128949869183170583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54428380085966579455447055 81642570128949869183170583)
          ·
            refine ⟨122463855193424803774755875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81642570128949869183170583 122463855193424803774755875)
            ·
              refine ⟨183695782790137205662133813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122463855193424803774755875 183695782790137205662133813)
              ·
                refine ⟨17221479636575363030825045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 183695782790137205662133813 17221479636575363030825045)
                ·
                  refine ⟨201814214491117535517481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17221479636575363030825045 201814214491117535517481)
                  ·
                    rfl

theorem cell22_1768643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 8].length) (baseStart_1768643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1768643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1768643 prefixEnd_1768643 := by exact prefixLift 1768643
  have htrace : WordTrace (prefixWord ++ tailWord_1768643) baseStart_1768643 baseEnd_1768643 := by
    simpa [prefixWord, tailWord_1768643, baseEnd_1768643] using wordTrace_append hprefix tailTrace_1768643
  have hstable : (prefixWord ++ tailWord_1768643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768643).length < 2 ^ (prefixWord ++ tailWord_1768643).sum := by decide
  have hdescent : baseEnd_1768643 < baseStart_1768643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768705 : List Nat := [1, 2, 4, 1, 1, 3, 2, 8]
def baseStart_1768705 : Nat := 118140960795 + 1768705 * 2 ^ 59
def prefixEnd_1768705 : Nat := 4983230072969 + 3 ^ 40 * 1768705 * 2
def baseEnd_1768705 : Nat := 67273763037822790166917

theorem tailTrace_1768705 : CollatzResearch.WordTrace tailWord_1768705 prefixEnd_1768705 67273763037822790166917 := by
  unfold tailWord_1768705
  simp only [CollatzResearch.WordTrace]
  refine ⟨64509971057291330610027569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43006647371527553740018379 64509971057291330610027569)
  ·
    refine ⟨48382478292968497957520677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64509971057291330610027569 48382478292968497957520677)
    ·
      refine ⟨9071714679931593367035127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48382478292968497957520677 9071714679931593367035127)
      ·
        refine ⟨13607572019897390050552691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9071714679931593367035127 13607572019897390050552691)
        ·
          refine ⟨20411358029846085075829037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13607572019897390050552691 20411358029846085075829037)
          ·
            refine ⟨7654259261192281903435889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20411358029846085075829037 7654259261192281903435889)
            ·
              refine ⟨5740694445894211427576917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7654259261192281903435889 5740694445894211427576917)
              ·
                refine ⟨67273763037822790166917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5740694445894211427576917 67273763037822790166917)
                ·
                  rfl

theorem cell22_1768705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 8].length) (baseStart_1768705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1768705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1768705 prefixEnd_1768705 := by exact prefixLift 1768705
  have htrace : WordTrace (prefixWord ++ tailWord_1768705) baseStart_1768705 baseEnd_1768705 := by
    simpa [prefixWord, tailWord_1768705, baseEnd_1768705] using wordTrace_append hprefix tailTrace_1768705
  have hstable : (prefixWord ++ tailWord_1768705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768705).length < 2 ^ (prefixWord ++ tailWord_1768705).sum := by decide
  have hdescent : baseEnd_1768705 < baseStart_1768705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768707 : List Nat := [1, 1, 1, 3, 2, 5, 2, 1, 2, 4]
def baseStart_1768707 : Nat := 118140960795 + 1768707 * 2 ^ 59
def prefixEnd_1768707 : Nat := 4983230072969 + 3 ^ 40 * 1768707 * 2
def baseEnd_1768707 : Nat := 605464551981277772952247

theorem tailTrace_1768707 : CollatzResearch.WordTrace tailWord_1768707 prefixEnd_1768707 605464551981277772952247 := by
  unfold tailWord_1768707
  simp only [CollatzResearch.WordTrace]
  refine ⟨64510044003284084951600375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43006696002189389967733583 64510044003284084951600375)
  ·
    refine ⟨96765066004926127427400563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64510044003284084951600375 96765066004926127427400563)
    ·
      refine ⟨145147599007389191141100845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96765066004926127427400563 145147599007389191141100845)
      ·
        refine ⟨54430349627770946677912817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145147599007389191141100845 54430349627770946677912817)
        ·
          refine ⟨40822762220828210008434613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54430349627770946677912817 40822762220828210008434613)
          ·
            refine ⟨3827133958202644688290745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40822762220828210008434613 3827133958202644688290745)
            ·
              refine ⟨2870350468651983516218059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3827133958202644688290745 2870350468651983516218059)
              ·
                refine ⟨4305525702977975274327089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2870350468651983516218059 4305525702977975274327089)
                ·
                  refine ⟨3229144277233481455745317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4305525702977975274327089 3229144277233481455745317)
                  ·
                    refine ⟨605464551981277772952247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3229144277233481455745317 605464551981277772952247)
                    ·
                      rfl

theorem cell22_1768707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 1, 2, 4].length) (baseStart_1768707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1768707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1768707 prefixEnd_1768707 := by exact prefixLift 1768707
  have htrace : WordTrace (prefixWord ++ tailWord_1768707) baseStart_1768707 baseEnd_1768707 := by
    simpa [prefixWord, tailWord_1768707, baseEnd_1768707] using wordTrace_append hprefix tailTrace_1768707
  have hstable : (prefixWord ++ tailWord_1768707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768707).length < 2 ^ (prefixWord ++ tailWord_1768707).sum := by decide
  have hdescent : baseEnd_1768707 < baseStart_1768707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768722 : List Nat := [3, 2, 4, 2, 11]
def baseStart_1768722 : Nat := 118140960795 + 1768722 * 2 ^ 59
def prefixEnd_1768722 : Nat := 4983230072969 + 3 ^ 40 * 1768722 * 2
def baseEnd_1768722 : Nat := 2491644801595978328507

theorem tailTrace_1768722 : CollatzResearch.WordTrace tailWord_1768722 prefixEnd_1768722 2491644801595978328507 := by
  unfold tailWord_1768722
  simp only [CollatzResearch.WordTrace]
  refine ⟨16127647774557435628349105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43007060732153161675597613 16127647774557435628349105)
  ·
    refine ⟨12095735830918076721261829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16127647774557435628349105 12095735830918076721261829)
    ·
      refine ⟨2267950468297139385236593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12095735830918076721261829 2267950468297139385236593)
      ·
        refine ⟨1700962851222854538927445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2267950468297139385236593 1700962851222854538927445)
        ·
          refine ⟨2491644801595978328507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1700962851222854538927445 2491644801595978328507)
          ·
            rfl

theorem cell22_1768722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 11].length) (baseStart_1768722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1768722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1768722 prefixEnd_1768722 := by exact prefixLift 1768722
  have htrace : WordTrace (prefixWord ++ tailWord_1768722) baseStart_1768722 baseEnd_1768722 := by
    simpa [prefixWord, tailWord_1768722, baseEnd_1768722] using wordTrace_append hprefix tailTrace_1768722
  have hstable : (prefixWord ++ tailWord_1768722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768722).length < 2 ^ (prefixWord ++ tailWord_1768722).sum := by decide
  have hdescent : baseEnd_1768722 < baseStart_1768722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768737 : List Nat := [1, 2, 3, 2, 1, 1, 1, 5, 3, 3]
def baseStart_1768737 : Nat := 118140960795 + 1768737 * 2 ^ 59
def prefixEnd_1768737 : Nat := 4983230072969 + 3 ^ 40 * 1768737 * 2
def baseEnd_1768737 : Nat := 605474821594367694702155

theorem tailTrace_1768737 : CollatzResearch.WordTrace tailWord_1768737 prefixEnd_1768737 605474821594367694702155 := by
  unfold tailWord_1768737
  simp only [CollatzResearch.WordTrace]
  refine ⟨64511138193175400075192465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43007425462116933383461643 64511138193175400075192465)
  ·
    refine ⟨48383353644881550056394349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64511138193175400075192465 48383353644881550056394349)
    ·
      refine ⟨18143757616830581271147881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48383353644881550056394349 18143757616830581271147881)
      ·
        refine ⟨13607818212622935953360911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18143757616830581271147881 13607818212622935953360911)
        ·
          refine ⟨20411727318934403930041367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13607818212622935953360911 20411727318934403930041367)
          ·
            refine ⟨30617590978401605895062051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20411727318934403930041367 30617590978401605895062051)
            ·
              refine ⟨45926386467602408842593077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30617590978401605895062051 45926386467602408842593077)
              ·
                refine ⟨4305598731337725828993101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45926386467602408842593077 4305598731337725828993101)
                ·
                  refine ⟨1614599524251647185872413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4305598731337725828993101 1614599524251647185872413)
                  ·
                    refine ⟨605474821594367694702155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1614599524251647185872413 605474821594367694702155)
                    ·
                      rfl

theorem cell22_1768737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5, 3, 3].length) (baseStart_1768737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1768737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1768737 prefixEnd_1768737 := by exact prefixLift 1768737
  have htrace : WordTrace (prefixWord ++ tailWord_1768737) baseStart_1768737 baseEnd_1768737 := by
    simpa [prefixWord, tailWord_1768737, baseEnd_1768737] using wordTrace_append hprefix tailTrace_1768737
  have hstable : (prefixWord ++ tailWord_1768737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768737).length < 2 ^ (prefixWord ++ tailWord_1768737).sum := by decide
  have hdescent : baseEnd_1768737 < baseStart_1768737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768754 : List Nat := [3, 2, 1, 1, 4, 2, 1, 2, 3, 3]
def baseStart_1768754 : Nat := 118140960795 + 1768754 * 2 ^ 59
def prefixEnd_1768754 : Nat := 4983230072969 + 3 ^ 40 * 1768754 * 2
def baseEnd_1768754 : Nat := 605480641041785317027103

theorem tailTrace_1768754 : CollatzResearch.WordTrace tailWord_1768754 prefixEnd_1768754 605480641041785317027103 := by
  unfold tailWord_1768754
  simp only [CollatzResearch.WordTrace]
  refine ⟨16127939558528452994640329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43007838822742541319040877 16127939558528452994640329)
  ·
    refine ⟨12095954668896339745980247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16127939558528452994640329 12095954668896339745980247)
    ·
      refine ⟨18143932003344509618970371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12095954668896339745980247 18143932003344509618970371)
      ·
        refine ⟨27215898005016764428455557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18143932003344509618970371 27215898005016764428455557)
        ·
          refine ⟨5102980875940643330335417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27215898005016764428455557 5102980875940643330335417)
          ·
            refine ⟨3827235656955482497751563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5102980875940643330335417 3827235656955482497751563)
            ·
              refine ⟨5740853485433223746627345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3827235656955482497751563 5740853485433223746627345)
              ·
                refine ⟨4305640114074917809970509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5740853485433223746627345 4305640114074917809970509)
                ·
                  refine ⟨1614615042778094178738941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4305640114074917809970509 1614615042778094178738941)
                  ·
                    refine ⟨605480641041785317027103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1614615042778094178738941 605480641041785317027103)
                    ·
                      rfl

theorem cell22_1768754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 2, 3, 3].length) (baseStart_1768754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1768754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1768754 prefixEnd_1768754 := by exact prefixLift 1768754
  have htrace : WordTrace (prefixWord ++ tailWord_1768754) baseStart_1768754 baseEnd_1768754 := by
    simpa [prefixWord, tailWord_1768754, baseEnd_1768754] using wordTrace_append hprefix tailTrace_1768754
  have hstable : (prefixWord ++ tailWord_1768754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768754).length < 2 ^ (prefixWord ++ tailWord_1768754).sum := by decide
  have hdescent : baseEnd_1768754 < baseStart_1768754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768758 : List Nat := [5, 1, 2, 3, 1, 2, 1, 1, 2, 4]
def baseStart_1768758 : Nat := 118140960795 + 1768758 * 2 ^ 59
def prefixEnd_1768758 : Nat := 4983230072969 + 3 ^ 40 * 1768758 * 2
def baseEnd_1768758 : Nat := 605482010323530639927091

theorem tailTrace_1768758 : CollatzResearch.WordTrace tailWord_1768758 prefixEnd_1768758 605482010323530639927091 := by
  unfold tailWord_1768758
  simp only [CollatzResearch.WordTrace]
  refine ⟨4031994007881207541356683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43007936084066213774471285 4031994007881207541356683)
  ·
    refine ⟨6047991011821811312035025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4031994007881207541356683 6047991011821811312035025)
    ·
      refine ⟨4535993258866358484026269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6047991011821811312035025 4535993258866358484026269)
      ·
        refine ⟨1700997472074884431509851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4535993258866358484026269 1700997472074884431509851)
        ·
          refine ⟨2551496208112326647264777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1700997472074884431509851 2551496208112326647264777)
          ·
            refine ⟨1913622156084244985448583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2551496208112326647264777 1913622156084244985448583)
            ·
              refine ⟨2870433234126367478172875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1913622156084244985448583 2870433234126367478172875)
              ·
                refine ⟨4305649851189551217259313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2870433234126367478172875 4305649851189551217259313)
                ·
                  refine ⟨3229237388392163412944485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4305649851189551217259313 3229237388392163412944485)
                  ·
                    refine ⟨605482010323530639927091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3229237388392163412944485 605482010323530639927091)
                    ·
                      rfl

theorem cell22_1768758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_1768758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1768758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1768758 prefixEnd_1768758 := by exact prefixLift 1768758
  have htrace : WordTrace (prefixWord ++ tailWord_1768758) baseStart_1768758 baseEnd_1768758 := by
    simpa [prefixWord, tailWord_1768758, baseEnd_1768758] using wordTrace_append hprefix tailTrace_1768758
  have hstable : (prefixWord ++ tailWord_1768758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768758).length < 2 ^ (prefixWord ++ tailWord_1768758).sum := by decide
  have hdescent : baseEnd_1768758 < baseStart_1768758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768812 : List Nat := [2, 2, 1, 1, 5, 1, 2, 2, 6]
def baseStart_1768812 : Nat := 118140960795 + 1768812 * 2 ^ 59
def prefixEnd_1768812 : Nat := 4983230072969 + 3 ^ 40 * 1768812 * 2
def baseEnd_1768812 : Nat := 201833498542364166358975

theorem tailTrace_1768812 : CollatzResearch.WordTrace tailWord_1768812 prefixEnd_1768812 201833498542364166358975 := by
  unfold tailWord_1768812
  simp only [CollatzResearch.WordTrace]
  refine ⟨32256936833951843942086345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43009249111935791922781793 32256936833951843942086345)
  ·
    refine ⟨24192702625463882956564759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32256936833951843942086345 24192702625463882956564759)
    ·
      refine ⟨36289053938195824434847139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24192702625463882956564759 36289053938195824434847139)
      ·
        refine ⟨54433580907293736652270709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36289053938195824434847139 54433580907293736652270709)
        ·
          refine ⟨5103148210058787811150379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54433580907293736652270709 5103148210058787811150379)
          ·
            refine ⟨7654722315088181716725569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5103148210058787811150379 7654722315088181716725569)
            ·
              refine ⟨5741041736316136287544177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7654722315088181716725569 5741041736316136287544177)
              ·
                refine ⟨4305781302237102215658133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5741041736316136287544177 4305781302237102215658133)
                ·
                  refine ⟨201833498542364166358975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4305781302237102215658133 201833498542364166358975)
                  ·
                    rfl

theorem cell22_1768812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 6].length) (baseStart_1768812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1768812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1768812 prefixEnd_1768812 := by exact prefixLift 1768812
  have htrace : WordTrace (prefixWord ++ tailWord_1768812) baseStart_1768812 baseEnd_1768812 := by
    simpa [prefixWord, tailWord_1768812, baseEnd_1768812] using wordTrace_append hprefix tailTrace_1768812
  have hstable : (prefixWord ++ tailWord_1768812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768812).length < 2 ^ (prefixWord ++ tailWord_1768812).sum := by decide
  have hdescent : baseEnd_1768812 < baseStart_1768812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768827 : List Nat := [1, 1, 1, 1, 1, 6, 1, 1, 6, 3]
def baseStart_1768827 : Nat := 118140960795 + 1768827 * 2 ^ 59
def prefixEnd_1768827 : Nat := 4983230072969 + 3 ^ 40 * 1768827 * 2
def baseEnd_1768827 : Nat := 605505630433637459951879

theorem tailTrace_1768827 : CollatzResearch.WordTrace tailWord_1768827 prefixEnd_1768827 605505630433637459951879 := by
  unfold tailWord_1768827
  simp only [CollatzResearch.WordTrace]
  refine ⟨64514420762849345445968735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43009613841899563630645823 64514420762849345445968735)
  ·
    refine ⟨96771631144274018168953103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64514420762849345445968735 96771631144274018168953103)
    ·
      refine ⟨145157446716411027253429655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96771631144274018168953103 145157446716411027253429655)
      ·
        refine ⟨217736170074616540880144483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145157446716411027253429655 217736170074616540880144483)
        ·
          refine ⟨326604255111924811320216725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217736170074616540880144483 326604255111924811320216725)
          ·
            refine ⟨15309574458371475530635159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 326604255111924811320216725 15309574458371475530635159)
            ·
              refine ⟨22964361687557213295952739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15309574458371475530635159 22964361687557213295952739)
              ·
                refine ⟨34446542531335819943929109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22964361687557213295952739 34446542531335819943929109)
                ·
                  refine ⟨1614681681156366559871677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 34446542531335819943929109 1614681681156366559871677)
                  ·
                    refine ⟨605505630433637459951879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1614681681156366559871677 605505630433637459951879)
                    ·
                      rfl

theorem cell22_1768827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 6, 3].length) (baseStart_1768827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1768827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1768827 prefixEnd_1768827 := by exact prefixLift 1768827
  have htrace : WordTrace (prefixWord ++ tailWord_1768827) baseStart_1768827 baseEnd_1768827 := by
    simpa [prefixWord, tailWord_1768827, baseEnd_1768827] using wordTrace_append hprefix tailTrace_1768827
  have hstable : (prefixWord ++ tailWord_1768827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768827).length < 2 ^ (prefixWord ++ tailWord_1768827).sum := by decide
  have hdescent : baseEnd_1768827 < baseStart_1768827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768844 : List Nat := [2, 2, 1, 2, 1, 3, 2, 4, 2, 3]
def baseStart_1768844 : Nat := 118140960795 + 1768844 * 2 ^ 59
def prefixEnd_1768844 : Nat := 4983230072969 + 3 ^ 40 * 1768844 * 2
def baseEnd_1768844 : Nat := 605511449881055082276827

theorem tailTrace_1768844 : CollatzResearch.WordTrace tailWord_1768844 prefixEnd_1768844 605511449881055082276827 := by
  unfold tailWord_1768844
  simp only [CollatzResearch.WordTrace]
  refine ⟨32257520401893878674668793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43010027202525171566225057 32257520401893878674668793)
  ·
    refine ⟨24193140301420409006001595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32257520401893878674668793 24193140301420409006001595)
    ·
      refine ⟨36289710452130613509002393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24193140301420409006001595 36289710452130613509002393)
      ·
        refine ⟨27217282839097960131751795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36289710452130613509002393 27217282839097960131751795)
        ·
          refine ⟨40825924258646940197627693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27217282839097960131751795 40825924258646940197627693)
          ·
            refine ⟨15309721596992602574110385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40825924258646940197627693 15309721596992602574110385)
            ·
              refine ⟨11482291197744451930582789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15309721596992602574110385 11482291197744451930582789)
              ·
                refine ⟨2152929599577084736984273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11482291197744451930582789 2152929599577084736984273)
                ·
                  refine ⟨1614697199682813552738205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2152929599577084736984273 1614697199682813552738205)
                  ·
                    refine ⟨605511449881055082276827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1614697199682813552738205 605511449881055082276827)
                    ·
                      rfl

theorem cell22_1768844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 4, 2, 3].length) (baseStart_1768844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1768844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1768844 prefixEnd_1768844 := by exact prefixLift 1768844
  have htrace : WordTrace (prefixWord ++ tailWord_1768844) baseStart_1768844 baseEnd_1768844 := by
    simpa [prefixWord, tailWord_1768844, baseEnd_1768844] using wordTrace_append hprefix tailTrace_1768844
  have hstable : (prefixWord ++ tailWord_1768844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768844).length < 2 ^ (prefixWord ++ tailWord_1768844).sum := by decide
  have hdescent : baseEnd_1768844 < baseStart_1768844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768846 : List Nat := [4, 1, 1, 4, 2, 2, 1, 1, 6]
def baseStart_1768846 : Nat := 118140960795 + 1768846 * 2 ^ 59
def prefixEnd_1768846 : Nat := 4983230072969 + 3 ^ 40 * 1768846 * 2
def baseEnd_1768846 : Nat := 201837378173975914575607

theorem tailTrace_1768846 : CollatzResearch.WordTrace tailWord_1768846 prefixEnd_1768846 201837378173975914575607 := by
  unfold tailWord_1768846
  simp only [CollatzResearch.WordTrace]
  refine ⟨8064389218722563961363799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43010075833187007793940261 8064389218722563961363799)
  ·
    refine ⟨12096583828083845942045699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8064389218722563961363799 12096583828083845942045699)
    ·
      refine ⟨18144875742125768913068549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12096583828083845942045699 18144875742125768913068549)
      ·
        refine ⟨3402164201648581671200353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18144875742125768913068549 3402164201648581671200353)
        ·
          refine ⟨2551623151236436253400265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3402164201648581671200353 2551623151236436253400265)
          ·
            refine ⟨1913717363427327190050199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2551623151236436253400265 1913717363427327190050199)
            ·
              refine ⟨2870576045140990785075299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1913717363427327190050199 2870576045140990785075299)
              ·
                refine ⟨4305864067711486177612949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2870576045140990785075299 4305864067711486177612949)
                ·
                  refine ⟨201837378173975914575607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4305864067711486177612949 201837378173975914575607)
                  ·
                    rfl

theorem cell22_1768846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 1, 6].length) (baseStart_1768846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1768846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1768846 prefixEnd_1768846 := by exact prefixLift 1768846
  have htrace : WordTrace (prefixWord ++ tailWord_1768846) baseStart_1768846 baseEnd_1768846 := by
    simpa [prefixWord, tailWord_1768846, baseEnd_1768846] using wordTrace_append hprefix tailTrace_1768846
  have hstable : (prefixWord ++ tailWord_1768846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768846).length < 2 ^ (prefixWord ++ tailWord_1768846).sum := by decide
  have hdescent : baseEnd_1768846 < baseStart_1768846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768857 : List Nat := [1, 2, 1, 2, 1, 6, 2, 7]
def baseStart_1768857 : Nat := 118140960795 + 1768857 * 2 ^ 59
def prefixEnd_1768857 : Nat := 4983230072969 + 3 ^ 40 * 1768857 * 2
def baseEnd_1768857 : Nat := 67279544449636375744643

theorem tailTrace_1768857 : CollatzResearch.WordTrace tailWord_1768857 prefixEnd_1768857 67279544449636375744643 := by
  unfold tailWord_1768857
  simp only [CollatzResearch.WordTrace]
  refine ⟨64515514952740660569560825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43010343301827107046373883 64515514952740660569560825)
  ·
    refine ⟨48386636214555495427170619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64515514952740660569560825 48386636214555495427170619)
    ·
      refine ⟨72579954321833243140755929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48386636214555495427170619 72579954321833243140755929)
      ·
        refine ⟨54434965741374932355566947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72579954321833243140755929 54434965741374932355566947)
        ·
          refine ⟨81652448612062398533350421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54434965741374932355566947 81652448612062398533350421)
          ·
            refine ⟨3827458528690424931250801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 81652448612062398533350421 3827458528690424931250801)
            ·
              refine ⟨2870593896517818698438101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3827458528690424931250801 2870593896517818698438101)
              ·
                refine ⟨67279544449636375744643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2870593896517818698438101 67279544449636375744643)
                ·
                  rfl

theorem cell22_1768857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 7].length) (baseStart_1768857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1768857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1768857 prefixEnd_1768857 := by exact prefixLift 1768857
  have htrace : WordTrace (prefixWord ++ tailWord_1768857) baseStart_1768857 baseEnd_1768857 := by
    simpa [prefixWord, tailWord_1768857, baseEnd_1768857] using wordTrace_append hprefix tailTrace_1768857
  have hstable : (prefixWord ++ tailWord_1768857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768857).length < 2 ^ (prefixWord ++ tailWord_1768857).sum := by decide
  have hdescent : baseEnd_1768857 < baseStart_1768857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768861 : List Nat := [1, 4, 2, 1, 3, 2, 1, 3, 2, 3]
def baseStart_1768861 : Nat := 118140960795 + 1768861 * 2 ^ 59
def prefixEnd_1768861 : Nat := 4983230072969 + 3 ^ 40 * 1768861 * 2
def baseEnd_1768861 : Nat := 605517269328472704601775

theorem tailTrace_1768861 : CollatzResearch.WordTrace tailWord_1768861 prefixEnd_1768861 605517269328472704601775 := by
  unfold tailWord_1768861
  simp only [CollatzResearch.WordTrace]
  refine ⟨64515660844726169252706437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43010440563150779501804291 64515660844726169252706437)
  ·
    refine ⟨12096686408386156734882457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64515660844726169252706437 12096686408386156734882457)
    ·
      refine ⟨9072514806289617551161843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12096686408386156734882457 9072514806289617551161843)
      ·
        refine ⟨13608772209434426326742765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9072514806289617551161843 13608772209434426326742765)
        ·
          refine ⟨5103289578537909872528537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13608772209434426326742765 5103289578537909872528537)
          ·
            refine ⟨3827467183903432404396403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5103289578537909872528537 3827467183903432404396403)
            ·
              refine ⟨5741200775855148606594605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3827467183903432404396403 5741200775855148606594605)
              ·
                refine ⟨2152950290945680727472977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5741200775855148606594605 2152950290945680727472977)
                ·
                  refine ⟨1614712718209260545604733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2152950290945680727472977 1614712718209260545604733)
                  ·
                    refine ⟨605517269328472704601775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1614712718209260545604733 605517269328472704601775)
                    ·
                      rfl

theorem cell22_1768861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_1768861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1768861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1768861 prefixEnd_1768861 := by exact prefixLift 1768861
  have htrace : WordTrace (prefixWord ++ tailWord_1768861) baseStart_1768861 baseEnd_1768861 := by
    simpa [prefixWord, tailWord_1768861, baseEnd_1768861] using wordTrace_append hprefix tailTrace_1768861
  have hstable : (prefixWord ++ tailWord_1768861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768861).length < 2 ^ (prefixWord ++ tailWord_1768861).sum := by decide
  have hdescent : baseEnd_1768861 < baseStart_1768861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768977 : List Nat := [1, 2, 2, 1, 1, 2, 3, 1, 3, 6]
def baseStart_1768977 : Nat := 118140960795 + 1768977 * 2 ^ 59
def prefixEnd_1768977 : Nat := 4983230072969 + 3 ^ 40 * 1768977 * 2
def baseEnd_1768977 : Nat := 605556978499087068701419

theorem tailTrace_1768977 : CollatzResearch.WordTrace tailWord_1768977 prefixEnd_1768977 605556978499087068701419 := by
  unfold tailWord_1768977
  simp only [CollatzResearch.WordTrace]
  refine ⟨64519891712305921063929185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43013261141537280709286123 64519891712305921063929185)
  ·
    refine ⟨48389918784229440797946889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64519891712305921063929185 48389918784229440797946889)
    ·
      refine ⟨36292439088172080598460167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48389918784229440797946889 36292439088172080598460167)
      ·
        refine ⟨54438658632258120897690251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36292439088172080598460167 54438658632258120897690251)
        ·
          refine ⟨81657987948387181346535377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54438658632258120897690251 81657987948387181346535377)
          ·
            refine ⟨61243490961290386009901533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81657987948387181346535377 61243490961290386009901533)
            ·
              refine ⟨22966309110483894753713075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61243490961290386009901533 22966309110483894753713075)
              ·
                refine ⟨34449463665725842130569613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22966309110483894753713075 34449463665725842130569613)
                ·
                  refine ⟨12918548874647190798963605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34449463665725842130569613 12918548874647190798963605)
                  ·
                    refine ⟨605556978499087068701419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12918548874647190798963605 605556978499087068701419)
                    ·
                      rfl

theorem cell22_1768977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 6].length) (baseStart_1768977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1768977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1768977 prefixEnd_1768977 := by exact prefixLift 1768977
  have htrace : WordTrace (prefixWord ++ tailWord_1768977) baseStart_1768977 baseEnd_1768977 := by
    simpa [prefixWord, tailWord_1768977, baseEnd_1768977] using wordTrace_append hprefix tailTrace_1768977
  have hstable : (prefixWord ++ tailWord_1768977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768977).length < 2 ^ (prefixWord ++ tailWord_1768977).sum := by decide
  have hdescent : baseEnd_1768977 < baseStart_1768977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768979 : List Nat := [1, 1, 1, 2, 1, 6, 3, 1, 1, 5]
def baseStart_1768979 : Nat := 118140960795 + 1768979 * 2 ^ 59
def prefixEnd_1768979 : Nat := 4983230072969 + 3 ^ 40 * 1768979 * 2
def baseEnd_1768979 : Nat := 605557663139959730151413

theorem tailTrace_1768979 : CollatzResearch.WordTrace tailWord_1768979 prefixEnd_1768979 605557663139959730151413 := by
  unfold tailWord_1768979
  simp only [CollatzResearch.WordTrace]
  refine ⟨64519964658298675405501991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43013309772199116937001327 64519964658298675405501991)
  ·
    refine ⟨96779946987448013108252987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64519964658298675405501991 96779946987448013108252987)
    ·
      refine ⟨145169920481172019662379481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96779946987448013108252987 145169920481172019662379481)
      ·
        refine ⟨108877440360879014746784611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145169920481172019662379481 108877440360879014746784611)
        ·
          refine ⟨163316160541318522120176917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108877440360879014746784611 163316160541318522120176917)
          ·
            refine ⟨7655445025374305724383293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 163316160541318522120176917 7655445025374305724383293)
            ·
              refine ⟨2870791884515364646643735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7655445025374305724383293 2870791884515364646643735)
              ·
                refine ⟨4306187826773046969965603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2870791884515364646643735 4306187826773046969965603)
                ·
                  refine ⟨6459281740159570454948405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4306187826773046969965603 6459281740159570454948405)
                  ·
                    refine ⟨605557663139959730151413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6459281740159570454948405 605557663139959730151413)
                    ·
                      rfl

theorem cell22_1768979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 1, 1, 5].length) (baseStart_1768979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1768979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1768979 prefixEnd_1768979 := by exact prefixLift 1768979
  have htrace : WordTrace (prefixWord ++ tailWord_1768979) baseStart_1768979 baseEnd_1768979 := by
    simpa [prefixWord, tailWord_1768979, baseEnd_1768979] using wordTrace_append hprefix tailTrace_1768979
  have hstable : (prefixWord ++ tailWord_1768979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768979).length < 2 ^ (prefixWord ++ tailWord_1768979).sum := by decide
  have hdescent : baseEnd_1768979 < baseStart_1768979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768994 : List Nat := [3, 3, 1, 1, 1, 1, 4, 1, 1, 6]
def baseStart_1768994 : Nat := 118140960795 + 1768994 * 2 ^ 59
def prefixEnd_1768994 : Nat := 4983230072969 + 3 ^ 40 * 1768994 * 2
def baseEnd_1768994 : Nat := 605562797946504691026367

theorem tailTrace_1768994 : CollatzResearch.WordTrace tailWord_1768994 prefixEnd_1768994 605562797946504691026367 := by
  unfold tailWord_1768994
  simp only [CollatzResearch.WordTrace]
  refine ⟨16130127938311083241824509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43013674502162888644865357 16130127938311083241824509)
  ·
    refine ⟨6048797976866656215684191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16130127938311083241824509 6048797976866656215684191)
    ·
      refine ⟨9073196965299984323526287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6048797976866656215684191 9073196965299984323526287)
      ·
        refine ⟨13609795447949976485289431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9073196965299984323526287 13609795447949976485289431)
        ·
          refine ⟨20414693171924964727934147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13609795447949976485289431 20414693171924964727934147)
          ·
            refine ⟨30622039757887447091901221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20414693171924964727934147 30622039757887447091901221)
            ·
              refine ⟨5741632454603896329731479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30622039757887447091901221 5741632454603896329731479)
              ·
                refine ⟨8612448681905844494597219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5741632454603896329731479 8612448681905844494597219)
                ·
                  refine ⟨12918673022858766741895829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8612448681905844494597219 12918673022858766741895829)
                  ·
                    refine ⟨605562797946504691026367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12918673022858766741895829 605562797946504691026367)
                    ·
                      rfl

theorem cell22_1768994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_1768994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1768994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1768994 prefixEnd_1768994 := by exact prefixLift 1768994
  have htrace : WordTrace (prefixWord ++ tailWord_1768994) baseStart_1768994 baseEnd_1768994 := by
    simpa [prefixWord, tailWord_1768994, baseEnd_1768994] using wordTrace_append hprefix tailTrace_1768994
  have hstable : (prefixWord ++ tailWord_1768994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768994).length < 2 ^ (prefixWord ++ tailWord_1768994).sum := by decide
  have hdescent : baseEnd_1768994 < baseStart_1768994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769099 : List Nat := [1, 1, 1, 1, 4, 1, 5, 2, 6]
def baseStart_1769099 : Nat := 118140960795 + 1769099 * 2 ^ 59
def prefixEnd_1769099 : Nat := 4983230072969 + 3 ^ 40 * 1769099 * 2
def baseEnd_1769099 : Nat := 201866247197439805717015

theorem tailTrace_1769099 : CollatzResearch.WordTrace tailWord_1769099 prefixEnd_1769099 201866247197439805717015 := by
  unfold tailWord_1769099
  simp only [CollatzResearch.WordTrace]
  refine ⟨64524341417863935899870351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43016227611909290599913567 64524341417863935899870351)
  ·
    refine ⟨96786512126795903849805527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64524341417863935899870351 96786512126795903849805527)
    ·
      refine ⟨145179768190193855774708291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96786512126795903849805527 145179768190193855774708291)
      ·
        refine ⟨217769652285290783662062437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145179768190193855774708291 217769652285290783662062437)
        ·
          refine ⟨40831809803492021936636707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 217769652285290783662062437 40831809803492021936636707)
          ·
            refine ⟨61247714705238032904955061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40831809803492021936636707 61247714705238032904955061)
            ·
              refine ⟨5741973253616065584839537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61247714705238032904955061 5741973253616065584839537)
              ·
                refine ⟨4306479940212049188629653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5741973253616065584839537 4306479940212049188629653)
                ·
                  refine ⟨201866247197439805717015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4306479940212049188629653 201866247197439805717015)
                  ·
                    rfl

theorem cell22_1769099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2, 6].length) (baseStart_1769099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1769099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1769099 prefixEnd_1769099 := by exact prefixLift 1769099
  have htrace : WordTrace (prefixWord ++ tailWord_1769099) baseStart_1769099 baseEnd_1769099 := by
    simpa [prefixWord, tailWord_1769099, baseEnd_1769099] using wordTrace_append hprefix tailTrace_1769099
  have hstable : (prefixWord ++ tailWord_1769099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769099).length < 2 ^ (prefixWord ++ tailWord_1769099).sum := by decide
  have hdescent : baseEnd_1769099 < baseStart_1769099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769122 : List Nat := [3, 3, 1, 4, 2, 1, 1, 2, 5]
def baseStart_1769122 : Nat := 118140960795 + 1769122 * 2 ^ 59
def prefixEnd_1769122 : Nat := 4983230072969 + 3 ^ 40 * 1769122 * 2
def baseEnd_1769122 : Nat := 201868871654118341275325

theorem tailTrace_1769122 : CollatzResearch.WordTrace tailWord_1769122 prefixEnd_1769122 201868871654118341275325 := by
  unfold tailWord_1769122
  simp only [CollatzResearch.WordTrace]
  refine ⟨16131295074195152706989405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43016786864520407218638413 16131295074195152706989405)
  ·
    refine ⟨6049235652823182265121027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16131295074195152706989405 6049235652823182265121027)
    ·
      refine ⟨9073853479234773397681541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6049235652823182265121027 9073853479234773397681541)
      ·
        refine ⟨1701347527356520012065289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9073853479234773397681541 1701347527356520012065289)
        ·
          refine ⟨1276010645517390009048967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1701347527356520012065289 1276010645517390009048967)
          ·
            refine ⟨1914015968276085013573451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1276010645517390009048967 1914015968276085013573451)
            ·
              refine ⟨2871023952414127520360177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1914015968276085013573451 2871023952414127520360177)
              ·
                refine ⟨2153267964310595640270133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2871023952414127520360177 2153267964310595640270133)
                ·
                  refine ⟨201868871654118341275325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2153267964310595640270133 201868871654118341275325)
                  ·
                    rfl

theorem cell22_1769122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_1769122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1769122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1769122 prefixEnd_1769122 := by exact prefixLift 1769122
  have htrace : WordTrace (prefixWord ++ tailWord_1769122) baseStart_1769122 baseEnd_1769122 := by
    simpa [prefixWord, tailWord_1769122, baseEnd_1769122] using wordTrace_append hprefix tailTrace_1769122
  have hstable : (prefixWord ++ tailWord_1769122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769122).length < 2 ^ (prefixWord ++ tailWord_1769122).sum := by decide
  have hdescent : baseEnd_1769122 < baseStart_1769122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769133 : List Nat := [1, 5, 2, 1, 1, 1, 1, 6, 4]
def baseStart_1769133 : Nat := 118140960795 + 1769133 * 2 ^ 59
def prefixEnd_1769133 : Nat := 4983230072969 + 3 ^ 40 * 1769133 * 2
def baseEnd_1769133 : Nat := 201870126829051553933647

theorem tailTrace_1769133 : CollatzResearch.WordTrace tailWord_1769133 prefixEnd_1769133 201870126829051553933647 := by
  unfold tailWord_1769133
  simp only [CollatzResearch.WordTrace]
  refine ⟨64525581499740759706608053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43017054333160506471072035 64525581499740759706608053)
  ·
    refine ⟨6049273265600696222494505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64525581499740759706608053 6049273265600696222494505)
    ·
      refine ⟨4536954949200522166870879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6049273265600696222494505 4536954949200522166870879)
      ·
        refine ⟨6805432423800783250306319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4536954949200522166870879 6805432423800783250306319)
        ·
          refine ⟨10208148635701174875459479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6805432423800783250306319 10208148635701174875459479)
          ·
            refine ⟨15312222953551762313189219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10208148635701174875459479 15312222953551762313189219)
            ·
              refine ⟨22968334430327643469783829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15312222953551762313189219 22968334430327643469783829)
              ·
                refine ⟨1076640676421608287646117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22968334430327643469783829 1076640676421608287646117)
                ·
                  refine ⟨201870126829051553933647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1076640676421608287646117 201870126829051553933647)
                  ·
                    rfl

theorem cell22_1769133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_1769133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1769133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1769133 prefixEnd_1769133 := by exact prefixLift 1769133
  have htrace : WordTrace (prefixWord ++ tailWord_1769133) baseStart_1769133 baseEnd_1769133 := by
    simpa [prefixWord, tailWord_1769133, baseEnd_1769133] using wordTrace_append hprefix tailTrace_1769133
  have hstable : (prefixWord ++ tailWord_1769133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769133).length < 2 ^ (prefixWord ++ tailWord_1769133).sum := by decide
  have hdescent : baseEnd_1769133 < baseStart_1769133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769148 : List Nat := [2, 2, 2, 3, 1, 4, 1, 1, 1, 5]
def baseStart_1769148 : Nat := 118140960795 + 1769148 * 2 ^ 59
def prefixEnd_1769148 : Nat := 4983230072969 + 3 ^ 40 * 1769148 * 2
def baseEnd_1769148 : Nat := 605615515293699622675895

theorem tailTrace_1769148 : CollatzResearch.WordTrace tailWord_1769148 prefixEnd_1769148 605615515293699622675895 := by
  unfold tailWord_1769148
  simp only [CollatzResearch.WordTrace]
  refine ⟨32263064297343208634202049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43017419063124278178936065 32263064297343208634202049)
  ·
    refine ⟨24197298223007406475651537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32263064297343208634202049 24197298223007406475651537)
    ·
      refine ⟨18147973667255554856738653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24197298223007406475651537 18147973667255554856738653)
      ·
        refine ⟨6805490125220833071276995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18147973667255554856738653 6805490125220833071276995)
        ·
          refine ⟨10208235187831249606915493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6805490125220833071276995 10208235187831249606915493)
          ·
            refine ⟨1914044097718359301296655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10208235187831249606915493 1914044097718359301296655)
            ·
              refine ⟨2871066146577538951944983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1914044097718359301296655 2871066146577538951944983)
              ·
                refine ⟨4306599219866308427917475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2871066146577538951944983 4306599219866308427917475)
                ·
                  refine ⟨6459898829799462641876213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4306599219866308427917475 6459898829799462641876213)
                  ·
                    refine ⟨605615515293699622675895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6459898829799462641876213 605615515293699622675895)
                    ·
                      rfl

theorem cell22_1769148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 1, 1, 5].length) (baseStart_1769148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1769148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1769148 prefixEnd_1769148 := by exact prefixLift 1769148
  have htrace : WordTrace (prefixWord ++ tailWord_1769148) baseStart_1769148 baseEnd_1769148 := by
    simpa [prefixWord, tailWord_1769148, baseEnd_1769148] using wordTrace_append hprefix tailTrace_1769148
  have hstable : (prefixWord ++ tailWord_1769148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769148).length < 2 ^ (prefixWord ++ tailWord_1769148).sum := by decide
  have hdescent : baseEnd_1769148 < baseStart_1769148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769159 : List Nat := [1, 1, 4, 1, 1, 1, 3, 1, 2, 7]
def baseStart_1769159 : Nat := 118140960795 + 1769159 * 2 ^ 59
def prefixEnd_1769159 : Nat := 4983230072969 + 3 ^ 40 * 1769159 * 2
def baseEnd_1769159 : Nat := 605619280818499260650861

theorem tailTrace_1769159 : CollatzResearch.WordTrace tailWord_1769159 prefixEnd_1769159 605619280818499260650861 := by
  unfold tailWord_1769159
  simp only [CollatzResearch.WordTrace]
  refine ⟨64526529797646566147054531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43017686531764377431369687 64526529797646566147054531)
  ·
    refine ⟨96789794696469849220581797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64526529797646566147054531 96789794696469849220581797)
    ·
      refine ⟨18148086505588096728859087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96789794696469849220581797 18148086505588096728859087)
      ·
        refine ⟨27222129758382145093288631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18148086505588096728859087 27222129758382145093288631)
        ·
          refine ⟨40833194637573217639932947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27222129758382145093288631 40833194637573217639932947)
          ·
            refine ⟨61249791956359826459899421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40833194637573217639932947 61249791956359826459899421)
            ·
              refine ⟨22968671983634934922462283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61249791956359826459899421 22968671983634934922462283)
              ·
                refine ⟨34453007975452402383693425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22968671983634934922462283 34453007975452402383693425)
                ·
                  refine ⟨25839755981589301787770069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34453007975452402383693425 25839755981589301787770069)
                  ·
                    refine ⟨605619280818499260650861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25839755981589301787770069 605619280818499260650861)
                    ·
                      rfl

theorem cell22_1769159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_1769159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1769159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1769159 prefixEnd_1769159 := by exact prefixLift 1769159
  have htrace : WordTrace (prefixWord ++ tailWord_1769159) baseStart_1769159 baseEnd_1769159 := by
    simpa [prefixWord, tailWord_1769159, baseEnd_1769159] using wordTrace_append hprefix tailTrace_1769159
  have hstable : (prefixWord ++ tailWord_1769159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769159).length < 2 ^ (prefixWord ++ tailWord_1769159).sum := by decide
  have hdescent : baseEnd_1769159 < baseStart_1769159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769165 : List Nat := [1, 6, 2, 1, 1, 1, 1, 2, 4, 3]
def baseStart_1769165 : Nat := 118140960795 + 1769165 * 2 ^ 59
def prefixEnd_1769165 : Nat := 4983230072969 + 3 ^ 40 * 1769165 * 2
def baseEnd_1769165 : Nat := 605621334741117245000843

theorem tailTrace_1769165 : CollatzResearch.WordTrace tailWord_1769165 prefixEnd_1769165 605621334741117245000843 := by
  unfold tailWord_1769165
  simp only [CollatzResearch.WordTrace]
  refine ⟨64526748635624829171772949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43017832423749886114515299 64526748635624829171772949)
  ·
    refine ⟨3024691342294913867426857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 64526748635624829171772949 3024691342294913867426857)
    ·
      refine ⟨2268518506721185400570143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3024691342294913867426857 2268518506721185400570143)
      ·
        refine ⟨3402777760081778100855215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2268518506721185400570143 3402777760081778100855215)
        ·
          refine ⟨5104166640122667151282823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3402777760081778100855215 5104166640122667151282823)
          ·
            refine ⟨7656249960184000726924235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5104166640122667151282823 7656249960184000726924235)
            ·
              refine ⟨11484374940276001090386353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7656249960184000726924235 11484374940276001090386353)
              ·
                refine ⟨8613281205207000817789765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11484374940276001090386353 8613281205207000817789765)
                ·
                  refine ⟨1614990225976312653335581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8613281205207000817789765 1614990225976312653335581)
                  ·
                    refine ⟨605621334741117245000843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1614990225976312653335581 605621334741117245000843)
                    ·
                      rfl

theorem cell22_1769165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_1769165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1769165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1769165 prefixEnd_1769165 := by exact prefixLift 1769165
  have htrace : WordTrace (prefixWord ++ tailWord_1769165) baseStart_1769165 baseEnd_1769165 := by
    simpa [prefixWord, tailWord_1769165, baseEnd_1769165] using wordTrace_append hprefix tailTrace_1769165
  have hstable : (prefixWord ++ tailWord_1769165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769165).length < 2 ^ (prefixWord ++ tailWord_1769165).sum := by decide
  have hdescent : baseEnd_1769165 < baseStart_1769165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769180 : List Nat := [2, 2, 5, 1, 2, 1, 1, 2, 2, 4]
def baseStart_1769180 : Nat := 118140960795 + 1769180 * 2 ^ 59
def prefixEnd_1769180 : Nat := 4983230072969 + 3 ^ 40 * 1769180 * 2
def baseEnd_1769180 : Nat := 605626469547662205875797

theorem tailTrace_1769180 : CollatzResearch.WordTrace tailWord_1769180 prefixEnd_1769180 605626469547662205875797 := by
  unfold tailWord_1769180
  simp only [CollatzResearch.WordTrace]
  refine ⟨32263647865285243366784497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43018197153713657822379329 32263647865285243366784497)
  ·
    refine ⟨24197735898963932525088373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32263647865285243366784497 24197735898963932525088373)
    ·
      refine ⟨2268537740527868674227035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24197735898963932525088373 2268537740527868674227035)
      ·
        refine ⟨3402806610791803011340553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2268537740527868674227035 3402806610791803011340553)
        ·
          refine ⟨2552104958093852258505415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3402806610791803011340553 2552104958093852258505415)
          ·
            refine ⟨3828157437140778387758123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2552104958093852258505415 3828157437140778387758123)
            ·
              refine ⟨5742236155711167581637185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3828157437140778387758123 5742236155711167581637185)
              ·
                refine ⟨4306677116783375686227889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5742236155711167581637185 4306677116783375686227889)
                ·
                  refine ⟨3230007837587531764670917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4306677116783375686227889 3230007837587531764670917)
                  ·
                    refine ⟨605626469547662205875797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3230007837587531764670917 605626469547662205875797)
                    ·
                      rfl

theorem cell22_1769180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_1769180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1769180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1769180 prefixEnd_1769180 := by exact prefixLift 1769180
  have htrace : WordTrace (prefixWord ++ tailWord_1769180) baseStart_1769180 baseEnd_1769180 := by
    simpa [prefixWord, tailWord_1769180, baseEnd_1769180] using wordTrace_append hprefix tailTrace_1769180
  have hstable : (prefixWord ++ tailWord_1769180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769180).length < 2 ^ (prefixWord ++ tailWord_1769180).sum := by decide
  have hdescent : baseEnd_1769180 < baseStart_1769180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769268 : List Nat := [2, 5, 1, 1, 2, 1, 1, 1, 8]
def baseStart_1769268 : Nat := 118140960795 + 1769268 * 2 ^ 59
def prefixEnd_1769268 : Nat := 4983230072969 + 3 ^ 40 * 1769268 * 2
def baseEnd_1769268 : Nat := 201885531248686436558509

theorem tailTrace_1769268 : CollatzResearch.WordTrace tailWord_1769268 prefixEnd_1769268 201885531248686436558509 := by
  unfold tailWord_1769268
  simp only [CollatzResearch.WordTrace]
  refine ⟨32265252677125838881386229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43020336902834451841848305 32265252677125838881386229)
  ·
    refine ⟨3024867438480547395129959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32265252677125838881386229 3024867438480547395129959)
    ·
      refine ⟨4537301157720821092694939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3024867438480547395129959 4537301157720821092694939)
      ·
        refine ⟨6805951736581231639042409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4537301157720821092694939 6805951736581231639042409)
        ·
          refine ⟨5104463802435923729281807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6805951736581231639042409 5104463802435923729281807)
          ·
            refine ⟨7656695703653885593922711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5104463802435923729281807 7656695703653885593922711)
            ·
              refine ⟨11485043555480828390884067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7656695703653885593922711 11485043555480828390884067)
              ·
                refine ⟨17227565333221242586326101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11485043555480828390884067 17227565333221242586326101)
                ·
                  refine ⟨201885531248686436558509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17227565333221242586326101 201885531248686436558509)
                  ·
                    rfl

theorem cell22_1769268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_1769268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1769268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1769268 prefixEnd_1769268 := by exact prefixLift 1769268
  have htrace : WordTrace (prefixWord ++ tailWord_1769268) baseStart_1769268 baseEnd_1769268 := by
    simpa [prefixWord, tailWord_1769268, baseEnd_1769268] using wordTrace_append hprefix tailTrace_1769268
  have hstable : (prefixWord ++ tailWord_1769268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769268).length < 2 ^ (prefixWord ++ tailWord_1769268).sum := by decide
  have hdescent : baseEnd_1769268 < baseStart_1769268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769270 : List Nat := [5, 1, 2, 2, 1, 1, 2, 1, 3, 4]
def baseStart_1769270 : Nat := 118140960795 + 1769270 * 2 ^ 59
def prefixEnd_1769270 : Nat := 4983230072969 + 3 ^ 40 * 1769270 * 2
def baseEnd_1769270 : Nat := 605657278386931971125521

theorem tailTrace_1769270 : CollatzResearch.WordTrace tailWord_1769270 prefixEnd_1769270 605657278386931971125521 := by
  unfold tailWord_1769270
  simp only [CollatzResearch.WordTrace]
  refine ⟨4033161143765277006521579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43020385533496288069563509 4033161143765277006521579)
  ·
    refine ⟨6049741715647915509782369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4033161143765277006521579 6049741715647915509782369)
    ·
      refine ⟨4537306286735936632336777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6049741715647915509782369 4537306286735936632336777)
      ·
        refine ⟨3402979715051952474252583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4537306286735936632336777 3402979715051952474252583)
        ·
          refine ⟨5104469572577928711378875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3402979715051952474252583 5104469572577928711378875)
          ·
            refine ⟨7656704358866893067068313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5104469572577928711378875 7656704358866893067068313)
            ·
              refine ⟨5742528269150169800301235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7656704358866893067068313 5742528269150169800301235)
              ·
                refine ⟨8613792403725254700451853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5742528269150169800301235 8613792403725254700451853)
                ·
                  refine ⟨3230172151396970512669445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8613792403725254700451853 3230172151396970512669445)
                  ·
                    refine ⟨605657278386931971125521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3230172151396970512669445 605657278386931971125521)
                    ·
                      rfl

theorem cell22_1769270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_1769270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1769270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1769270 prefixEnd_1769270 := by exact prefixLift 1769270
  have htrace : WordTrace (prefixWord ++ tailWord_1769270) baseStart_1769270 baseEnd_1769270 := by
    simpa [prefixWord, tailWord_1769270, baseEnd_1769270] using wordTrace_append hprefix tailTrace_1769270
  have hstable : (prefixWord ++ tailWord_1769270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769270).length < 2 ^ (prefixWord ++ tailWord_1769270).sum := by decide
  have hdescent : baseEnd_1769270 < baseStart_1769270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769300 : List Nat := [2, 4, 1, 1, 3, 2, 1, 1, 4, 3]
def baseStart_1769300 : Nat := 118140960795 + 1769300 * 2 ^ 59
def prefixEnd_1769300 : Nat := 4983230072969 + 3 ^ 40 * 1769300 * 2
def baseEnd_1769300 : Nat := 605667548000021892875429

theorem tailTrace_1769300 : CollatzResearch.WordTrace tailWord_1769300 prefixEnd_1769300 605667548000021892875429 := by
  unfold tailWord_1769300
  simp only [CollatzResearch.WordTrace]
  refine ⟨32265836245067873613968677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43021114993423831485291569 32265836245067873613968677)
  ·
    refine ⟨6049844295950226302619127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32265836245067873613968677 6049844295950226302619127)
    ·
      refine ⟨9074766443925339453928691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6049844295950226302619127 9074766443925339453928691)
      ·
        refine ⟨13612149665888009180893037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9074766443925339453928691 13612149665888009180893037)
        ·
          refine ⟨5104556124708003442834889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13612149665888009180893037 5104556124708003442834889)
          ·
            refine ⟨3828417093531002582126167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5104556124708003442834889 3828417093531002582126167)
            ·
              refine ⟨5742625640296503873189251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3828417093531002582126167 5742625640296503873189251)
              ·
                refine ⟨8613938460444755809783877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5742625640296503873189251 8613938460444755809783877)
                ·
                  refine ⟨1615113461333391714334477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8613938460444755809783877 1615113461333391714334477)
                  ·
                    refine ⟨605667548000021892875429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1615113461333391714334477 605667548000021892875429)
                    ·
                      rfl

theorem cell22_1769300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_1769300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1769300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1769300 prefixEnd_1769300 := by exact prefixLift 1769300
  have htrace : WordTrace (prefixWord ++ tailWord_1769300) baseStart_1769300 baseEnd_1769300 := by
    simpa [prefixWord, tailWord_1769300, baseEnd_1769300] using wordTrace_append hprefix tailTrace_1769300
  have hstable : (prefixWord ++ tailWord_1769300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769300).length < 2 ^ (prefixWord ++ tailWord_1769300).sum := by decide
  have hdescent : baseEnd_1769300 < baseStart_1769300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769362 : List Nat := [3, 2, 3, 2, 1, 1, 3, 1, 3, 3]
def baseStart_1769362 : Nat := 118140960795 + 1769362 * 2 ^ 59
def prefixEnd_1769362 : Nat := 4983230072969 + 3 ^ 40 * 1769362 * 2
def baseEnd_1769362 : Nat := 605688771867074397825239

theorem tailTrace_1769362 : CollatzResearch.WordTrace tailWord_1769362 prefixEnd_1769362 605688771867074397825239 := by
  unfold tailWord_1769362
  simp only [CollatzResearch.WordTrace]
  refine ⟨16133483453977782954173585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43022622543940754544462893 16133483453977782954173585)
  ·
    refine ⟨12100112590483337215630189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16133483453977782954173585 12100112590483337215630189)
    ·
      refine ⟨4537542221431251455861321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12100112590483337215630189 4537542221431251455861321)
      ·
        refine ⟨3403156666073438591895991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4537542221431251455861321 3403156666073438591895991)
        ·
          refine ⟨5104734999110157887843987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3403156666073438591895991 5104734999110157887843987)
          ·
            refine ⟨7657102498665236831765981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5104734999110157887843987 7657102498665236831765981)
            ·
              refine ⟨2871413436999463811912243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7657102498665236831765981 2871413436999463811912243)
              ·
                refine ⟨4307120155499195717868365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2871413436999463811912243 4307120155499195717868365)
                ·
                  refine ⟨1615170058312198394200637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4307120155499195717868365 1615170058312198394200637)
                  ·
                    refine ⟨605688771867074397825239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1615170058312198394200637 605688771867074397825239)
                    ·
                      rfl

theorem cell22_1769362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_1769362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1769362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1769362 prefixEnd_1769362 := by exact prefixLift 1769362
  have htrace : WordTrace (prefixWord ++ tailWord_1769362) baseStart_1769362 baseEnd_1769362 := by
    simpa [prefixWord, tailWord_1769362, baseEnd_1769362] using wordTrace_append hprefix tailTrace_1769362
  have hstable : (prefixWord ++ tailWord_1769362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769362).length < 2 ^ (prefixWord ++ tailWord_1769362).sum := by decide
  have hdescent : baseEnd_1769362 < baseStart_1769362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769375 : List Nat := [1, 1, 2, 5, 3, 1, 1, 3, 5]
def baseStart_1769375 : Nat := 118140960795 + 1769375 * 2 ^ 59
def prefixEnd_1769375 : Nat := 4983230072969 + 3 ^ 40 * 1769375 * 2
def baseEnd_1769375 : Nat := 201897740677582232416733

theorem tailTrace_1769375 : CollatzResearch.WordTrace tailWord_1769375 prefixEnd_1769375 201897740677582232416733 := by
  unfold tailWord_1769375
  simp only [CollatzResearch.WordTrace]
  refine ⟨64534407964864035036917579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43022938643242690024611719 64534407964864035036917579)
  ·
    refine ⟨96801611947296052555376369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64534407964864035036917579 96801611947296052555376369)
    ·
      refine ⟨72601208960472039416532277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96801611947296052555376369 72601208960472039416532277)
      ·
        refine ⟨6806363340044253695299901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72601208960472039416532277 6806363340044253695299901)
        ·
          refine ⟨2552386252516595135737463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6806363340044253695299901 2552386252516595135737463)
          ·
            refine ⟨3828579378774892703606195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2552386252516595135737463 3828579378774892703606195)
            ·
              refine ⟨5742869068162339055409293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3828579378774892703606195 5742869068162339055409293)
              ·
                refine ⟨2153575900560877145778485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5742869068162339055409293 2153575900560877145778485)
                ·
                  refine ⟨201897740677582232416733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2153575900560877145778485 201897740677582232416733)
                  ·
                    rfl

theorem cell22_1769375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 3, 5].length) (baseStart_1769375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1769375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1769375 prefixEnd_1769375 := by exact prefixLift 1769375
  have htrace : WordTrace (prefixWord ++ tailWord_1769375) baseStart_1769375 baseEnd_1769375 := by
    simpa [prefixWord, tailWord_1769375, baseEnd_1769375] using wordTrace_append hprefix tailTrace_1769375
  have hstable : (prefixWord ++ tailWord_1769375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769375).length < 2 ^ (prefixWord ++ tailWord_1769375).sum := by decide
  have hdescent : baseEnd_1769375 < baseStart_1769375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769542 : List Nat := [6, 1, 1, 1, 1, 1, 2, 1, 1, 7]
def baseStart_1769542 : Nat := 118140960795 + 1769542 * 2 ^ 59
def prefixEnd_1769542 : Nat := 4983230072969 + 3 ^ 40 * 1769542 * 2
def baseEnd_1769542 : Nat := 605750389545613928324687

theorem tailTrace_1769542 : CollatzResearch.WordTrace tailWord_1769542 prefixEnd_1769542 605750389545613928324687 := by
  unfold tailWord_1769542
  simp only [CollatzResearch.WordTrace]
  refine ⟨2016890592351844454945215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 43026999303506015038831253 2016890592351844454945215)
  ·
    refine ⟨3025335888527766682417823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2016890592351844454945215 3025335888527766682417823)
    ·
      refine ⟨4538003832791650023626735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3025335888527766682417823 4538003832791650023626735)
      ·
        refine ⟨6807005749187475035440103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4538003832791650023626735 6807005749187475035440103)
        ·
          refine ⟨10210508623781212553160155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6807005749187475035440103 10210508623781212553160155)
          ·
            refine ⟨15315762935671818829740233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10210508623781212553160155 15315762935671818829740233)
            ·
              refine ⟨11486822201753864122305175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15315762935671818829740233 11486822201753864122305175)
              ·
                refine ⟨17230233302630796183457763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11486822201753864122305175 17230233302630796183457763)
                ·
                  refine ⟨25845349953946194275186645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17230233302630796183457763 25845349953946194275186645)
                  ·
                    refine ⟨605750389545613928324687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25845349953946194275186645 605750389545613928324687)
                    ·
                      rfl

theorem cell22_1769542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_1769542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1769542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1769542 prefixEnd_1769542 := by exact prefixLift 1769542
  have htrace : WordTrace (prefixWord ++ tailWord_1769542) baseStart_1769542 baseEnd_1769542 := by
    simpa [prefixWord, tailWord_1769542, baseEnd_1769542] using wordTrace_append hprefix tailTrace_1769542
  have hstable : (prefixWord ++ tailWord_1769542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769542).length < 2 ^ (prefixWord ++ tailWord_1769542).sum := by decide
  have hdescent : baseEnd_1769542 < baseStart_1769542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769557 : List Nat := [1, 3, 2, 2, 1, 3, 3, 2, 1, 4]
def baseStart_1769557 : Nat := 118140960795 + 1769557 * 2 ^ 59
def prefixEnd_1769557 : Nat := 4983230072969 + 3 ^ 40 * 1769557 * 2
def baseEnd_1769557 : Nat := 605755524352158889199641

theorem tailTrace_1769557 : CollatzResearch.WordTrace tailWord_1769557 prefixEnd_1769557 605755524352158889199641 := by
  unfold tailWord_1769557
  simp only [CollatzResearch.WordTrace]
  refine ⟨64541046050204680120042925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43027364033469786746695283 64541046050204680120042925)
  ·
    refine ⟨24202892268826755045016097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64541046050204680120042925 24202892268826755045016097)
    ·
      refine ⟨18152169201620066283762073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24202892268826755045016097 18152169201620066283762073)
      ·
        refine ⟨13614126901215049712821555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18152169201620066283762073 13614126901215049712821555)
        ·
          refine ⟨20421190351822574569232333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13614126901215049712821555 20421190351822574569232333)
          ·
            refine ⟨7657946381933465463462125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20421190351822574569232333 7657946381933465463462125)
            ·
              refine ⟨2871729893225049548798297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7657946381933465463462125 2871729893225049548798297)
              ·
                refine ⟨2153797419918787161598723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2871729893225049548798297 2153797419918787161598723)
                ·
                  refine ⟨3230696129878180742398085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2153797419918787161598723 3230696129878180742398085)
                  ·
                    refine ⟨605755524352158889199641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3230696129878180742398085 605755524352158889199641)
                    ·
                      rfl

theorem cell22_1769557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 2, 1, 4].length) (baseStart_1769557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1769557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1769557 prefixEnd_1769557 := by exact prefixLift 1769557
  have htrace : WordTrace (prefixWord ++ tailWord_1769557) baseStart_1769557 baseEnd_1769557 := by
    simpa [prefixWord, tailWord_1769557, baseEnd_1769557] using wordTrace_append hprefix tailTrace_1769557
  have hstable : (prefixWord ++ tailWord_1769557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769557).length < 2 ^ (prefixWord ++ tailWord_1769557).sum := by decide
  have hdescent : baseEnd_1769557 < baseStart_1769557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769583 : List Nat := [1, 1, 2, 1, 3, 14]
def baseStart_1769583 : Nat := 118140960795 + 1769583 * 2 ^ 59
def prefixEnd_1769583 : Nat := 4983230072969 + 3 ^ 40 * 1769583 * 2
def baseEnd_1769583 : Nat := 7478573144240783803081

theorem tailTrace_1769583 : CollatzResearch.WordTrace tailWord_1769583 prefixEnd_1769583 7478573144240783803081 := by
  unfold tailWord_1769583
  simp only [CollatzResearch.WordTrace]
  refine ⟨64541994348110486560489403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43027996232073657706992935 64541994348110486560489403)
  ·
    refine ⟨96812991522165729840734105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64541994348110486560489403 96812991522165729840734105)
    ·
      refine ⟨72609743641624297380550579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96812991522165729840734105 72609743641624297380550579)
      ·
        refine ⟨108914615462436446070825869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72609743641624297380550579 108914615462436446070825869)
        ·
          refine ⟨40842980798413667276559701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108914615462436446070825869 40842980798413667276559701)
          ·
            refine ⟨7478573144240783803081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 40842980798413667276559701 7478573144240783803081)
            ·
              rfl

theorem cell22_1769583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 14].length) (baseStart_1769583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1769583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1769583 prefixEnd_1769583 := by exact prefixLift 1769583
  have htrace : WordTrace (prefixWord ++ tailWord_1769583) baseStart_1769583 baseEnd_1769583 := by
    simpa [prefixWord, tailWord_1769583, baseEnd_1769583] using wordTrace_append hprefix tailTrace_1769583
  have hstable : (prefixWord ++ tailWord_1769583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769583).length < 2 ^ (prefixWord ++ tailWord_1769583).sum := by decide
  have hdescent : baseEnd_1769583 < baseStart_1769583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769585 : List Nat := [1, 2, 2, 2, 1, 1, 3, 4, 2, 4]
def baseStart_1769585 : Nat := 118140960795 + 1769585 * 2 ^ 59
def prefixEnd_1769585 : Nat := 4983230072969 + 3 ^ 40 * 1769585 * 2
def baseEnd_1769585 : Nat := 605765109324376149499555

theorem tailTrace_1769585 : CollatzResearch.WordTrace tailWord_1769585 prefixEnd_1769585 605765109324376149499555 := by
  unfold tailWord_1769585
  simp only [CollatzResearch.WordTrace]
  refine ⟨64542067294103240902062209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43028044862735493934708139 64542067294103240902062209)
  ·
    refine ⟨48406550470577430676546657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64542067294103240902062209 48406550470577430676546657)
    ·
      refine ⟨36304912852933073007409993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48406550470577430676546657 36304912852933073007409993)
      ·
        refine ⟨27228684639699804755557495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36304912852933073007409993 27228684639699804755557495)
        ·
          refine ⟨40843026959549707133336243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27228684639699804755557495 40843026959549707133336243)
          ·
            refine ⟨61264540439324560700004365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40843026959549707133336243 61264540439324560700004365)
            ·
              refine ⟨22974202664746710262501637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61264540439324560700004365 22974202664746710262501637)
              ·
                refine ⟨4307662999640008174219057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22974202664746710262501637 4307662999640008174219057)
                ·
                  refine ⟨3230747249730006130664293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4307662999640008174219057 3230747249730006130664293)
                  ·
                    refine ⟨605765109324376149499555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3230747249730006130664293 605765109324376149499555)
                    ·
                      rfl

theorem cell22_1769585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4, 2, 4].length) (baseStart_1769585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1769585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1769585 prefixEnd_1769585 := by exact prefixLift 1769585
  have htrace : WordTrace (prefixWord ++ tailWord_1769585) baseStart_1769585 baseEnd_1769585 := by
    simpa [prefixWord, tailWord_1769585, baseEnd_1769585] using wordTrace_append hprefix tailTrace_1769585
  have hstable : (prefixWord ++ tailWord_1769585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769585).length < 2 ^ (prefixWord ++ tailWord_1769585).sum := by decide
  have hdescent : baseEnd_1769585 < baseStart_1769585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769690 : List Nat := [3, 1, 1, 2, 2, 1, 2, 2, 8]
def baseStart_1769690 : Nat := 118140960795 + 1769690 * 2 ^ 59
def prefixEnd_1769690 : Nat := 4983230072969 + 3 ^ 40 * 1769690 * 2
def baseEnd_1769690 : Nat := 201933684323396958541411

theorem tailTrace_1769690 : CollatzResearch.WordTrace tailWord_1769690 prefixEnd_1769690 201933684323396958541411 := by
  unfold tailWord_1769690
  simp only [CollatzResearch.WordTrace]
  refine ⟨16136474239680710958658631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43030597972481895889756349 16136474239680710958658631)
  ·
    refine ⟨24204711359521066437987947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16136474239680710958658631 24204711359521066437987947)
    ·
      refine ⟨36307067039281599656981921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24204711359521066437987947 36307067039281599656981921)
      ·
        refine ⟨27230300279461199742736441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36307067039281599656981921 27230300279461199742736441)
        ·
          refine ⟨20422725209595899807052331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27230300279461199742736441 20422725209595899807052331)
          ·
            refine ⟨30634087814393849710578497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20422725209595899807052331 30634087814393849710578497)
            ·
              refine ⟨22975565860795387282933873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30634087814393849710578497 22975565860795387282933873)
              ·
                refine ⟨17231674395596540462200405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22975565860795387282933873 17231674395596540462200405)
                ·
                  refine ⟨201933684323396958541411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17231674395596540462200405 201933684323396958541411)
                  ·
                    rfl

theorem cell22_1769690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 8].length) (baseStart_1769690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1769690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1769690 prefixEnd_1769690 := by exact prefixLift 1769690
  have htrace : WordTrace (prefixWord ++ tailWord_1769690) baseStart_1769690 baseEnd_1769690 := by
    simpa [prefixWord, tailWord_1769690, baseEnd_1769690] using wordTrace_append hprefix tailTrace_1769690
  have hstable : (prefixWord ++ tailWord_1769690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769690).length < 2 ^ (prefixWord ++ tailWord_1769690).sum := by decide
  have hdescent : baseEnd_1769690 < baseStart_1769690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769705 : List Nat := [1, 2, 1, 1, 1, 2, 2, 4, 3, 5]
def baseStart_1769705 : Nat := 118140960795 + 1769705 * 2 ^ 59
def prefixEnd_1769705 : Nat := 4983230072969 + 3 ^ 40 * 1769705 * 2
def baseEnd_1769705 : Nat := 605806187776735836499187

theorem tailTrace_1769705 : CollatzResearch.WordTrace tailWord_1769705 prefixEnd_1769705 605806187776735836499187 := by
  unfold tailWord_1769705
  simp only [CollatzResearch.WordTrace]
  refine ⟨64546444053668501396430569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43030962702445667597620379 64546444053668501396430569)
  ·
    refine ⟨48409833040251376047322927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64546444053668501396430569 48409833040251376047322927)
    ·
      refine ⟨72614749560377064070984391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48409833040251376047322927 72614749560377064070984391)
      ·
        refine ⟨108922124340565596106476587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72614749560377064070984391 108922124340565596106476587)
        ·
          refine ⟨163383186510848394159714881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108922124340565596106476587 163383186510848394159714881)
          ·
            refine ⟨122537389883136295619786161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163383186510848394159714881 122537389883136295619786161)
            ·
              refine ⟨91903042412352221714839621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122537389883136295619786161 91903042412352221714839621)
              ·
                refine ⟨17231820452316041571532429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91903042412352221714839621 17231820452316041571532429)
                ·
                  refine ⟨6461932669618515589324661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17231820452316041571532429 6461932669618515589324661)
                  ·
                    refine ⟨605806187776735836499187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6461932669618515589324661 605806187776735836499187)
                    ·
                      rfl

theorem cell22_1769705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3, 5].length) (baseStart_1769705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1769705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1769705 prefixEnd_1769705 := by exact prefixLift 1769705
  have htrace : WordTrace (prefixWord ++ tailWord_1769705) baseStart_1769705 baseEnd_1769705 := by
    simpa [prefixWord, tailWord_1769705, baseEnd_1769705] using wordTrace_append hprefix tailTrace_1769705
  have hstable : (prefixWord ++ tailWord_1769705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769705).length < 2 ^ (prefixWord ++ tailWord_1769705).sum := by decide
  have hdescent : baseEnd_1769705 < baseStart_1769705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769720 : List Nat := [2, 1, 2, 1, 1, 2, 1, 3, 3, 6]
def baseStart_1769720 : Nat := 118140960795 + 1769720 * 2 ^ 59
def prefixEnd_1769720 : Nat := 4983230072969 + 3 ^ 40 * 1769720 * 2
def baseEnd_1769720 : Nat := 605811322583280797374141

theorem tailTrace_1769720 : CollatzResearch.WordTrace tailWord_1769720 prefixEnd_1769720 605811322583280797374141 := by
  unfold tailWord_1769720
  simp only [CollatzResearch.WordTrace]
  refine ⟨32273495574307079479113307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43031327432409439305484409 32273495574307079479113307)
  ·
    refine ⟨48410243361460619218669961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32273495574307079479113307 48410243361460619218669961)
    ·
      refine ⟨36307682521095464414002471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48410243361460619218669961 36307682521095464414002471)
      ·
        refine ⟨54461523781643196621003707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36307682521095464414002471 54461523781643196621003707)
        ·
          refine ⟨81692285672464794931505561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54461523781643196621003707 81692285672464794931505561)
          ·
            refine ⟨61269214254348596198629171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81692285672464794931505561 61269214254348596198629171)
            ·
              refine ⟨91903821381522894297943757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61269214254348596198629171 91903821381522894297943757)
              ·
                refine ⟨34463933018071085361728909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91903821381522894297943757 34463933018071085361728909)
                ·
                  refine ⟨12923974881776657010648341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34463933018071085361728909 12923974881776657010648341)
                  ·
                    refine ⟨605811322583280797374141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12923974881776657010648341 605811322583280797374141)
                    ·
                      rfl

theorem cell22_1769720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 3, 6].length) (baseStart_1769720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1769720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1769720 prefixEnd_1769720 := by exact prefixLift 1769720
  have htrace : WordTrace (prefixWord ++ tailWord_1769720) baseStart_1769720 baseEnd_1769720 := by
    simpa [prefixWord, tailWord_1769720, baseEnd_1769720] using wordTrace_append hprefix tailTrace_1769720
  have hstable : (prefixWord ++ tailWord_1769720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769720).length < 2 ^ (prefixWord ++ tailWord_1769720).sum := by decide
  have hdescent : baseEnd_1769720 < baseStart_1769720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769737 : List Nat := [1, 2, 1, 1, 3, 4, 1, 3, 2, 4]
def baseStart_1769737 : Nat := 118140960795 + 1769737 * 2 ^ 59
def prefixEnd_1769737 : Nat := 4983230072969 + 3 ^ 40 * 1769737 * 2
def baseEnd_1769737 : Nat := 605817142030698419699089

theorem tailTrace_1769737 : CollatzResearch.WordTrace tailWord_1769737 prefixEnd_1769737 605817142030698419699089 := by
  unfold tailWord_1769737
  simp only [CollatzResearch.WordTrace]
  refine ⟨64547611189552570861595465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43031740793035047241063643 64547611189552570861595465)
  ·
    refine ⟨48410708392164428146196599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64547611189552570861595465 48410708392164428146196599)
    ·
      refine ⟨72616062588246642219294899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48410708392164428146196599 72616062588246642219294899)
      ·
        refine ⟨108924093882369963328942349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72616062588246642219294899 108924093882369963328942349)
        ·
          refine ⟨40846535205888736248353381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108924093882369963328942349 40846535205888736248353381)
          ·
            refine ⟨7658725351104138046566259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40846535205888736248353381 7658725351104138046566259)
            ·
              refine ⟨11488088026656207069849389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7658725351104138046566259 11488088026656207069849389)
              ·
                refine ⟨4308033009996077651193521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11488088026656207069849389 4308033009996077651193521)
                ·
                  refine ⟨3231024757497058238395141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4308033009996077651193521 3231024757497058238395141)
                  ·
                    refine ⟨605817142030698419699089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3231024757497058238395141 605817142030698419699089)
                    ·
                      rfl

theorem cell22_1769737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3, 2, 4].length) (baseStart_1769737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1769737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1769737 prefixEnd_1769737 := by exact prefixLift 1769737
  have htrace : WordTrace (prefixWord ++ tailWord_1769737) baseStart_1769737 baseEnd_1769737 := by
    simpa [prefixWord, tailWord_1769737, baseEnd_1769737] using wordTrace_append hprefix tailTrace_1769737
  have hstable : (prefixWord ++ tailWord_1769737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769737).length < 2 ^ (prefixWord ++ tailWord_1769737).sum := by decide
  have hdescent : baseEnd_1769737 < baseStart_1769737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769758 : List Nat := [4, 3, 2, 1, 1, 2, 1, 4, 4]
def baseStart_1769758 : Nat := 118140960795 + 1769758 * 2 ^ 59
def prefixEnd_1769758 : Nat := 4983230072969 + 3 ^ 40 * 1769758 * 2
def baseEnd_1769758 : Nat := 201941443586620454974675

theorem tailTrace_1769758 : CollatzResearch.WordTrace tailWord_1769758 prefixEnd_1769758 201941443586620454974675 := by
  unfold tailWord_1769758
  simp only [CollatzResearch.WordTrace]
  refine ⟨8068547140309561431013741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43032251414984327632073285 8068547140309561431013741)
  ·
    refine ⟨3025705177616085536630153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8068547140309561431013741 3025705177616085536630153)
    ·
      refine ⟨2269278883212064152472615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3025705177616085536630153 2269278883212064152472615)
      ·
        refine ⟨3403918324818096228708923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2269278883212064152472615 3403918324818096228708923)
        ·
          refine ⟨5105877487227144343063385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3403918324818096228708923 5105877487227144343063385)
          ·
            refine ⟨3829408115420358257297539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5105877487227144343063385 3829408115420358257297539)
            ·
              refine ⟨5744112173130537385946309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3829408115420358257297539 5744112173130537385946309)
              ·
                refine ⟨1077021032461975759864933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5744112173130537385946309 1077021032461975759864933)
                ·
                  refine ⟨201941443586620454974675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1077021032461975759864933 201941443586620454974675)
                  ·
                    rfl

theorem cell22_1769758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_1769758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1769758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1769758 prefixEnd_1769758 := by exact prefixLift 1769758
  have htrace : WordTrace (prefixWord ++ tailWord_1769758) baseStart_1769758 baseEnd_1769758 := by
    simpa [prefixWord, tailWord_1769758, baseEnd_1769758] using wordTrace_append hprefix tailTrace_1769758
  have hstable : (prefixWord ++ tailWord_1769758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769758).length < 2 ^ (prefixWord ++ tailWord_1769758).sum := by decide
  have hdescent : baseEnd_1769758 < baseStart_1769758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769831 : List Nat := [1, 1, 5, 1, 3, 2, 3, 1, 5]
def baseStart_1769831 : Nat := 118140960795 + 1769831 * 2 ^ 59
def prefixEnd_1769831 : Nat := 4983230072969 + 3 ^ 40 * 1769831 * 2
def baseEnd_1769831 : Nat := 201949773383904502616267

theorem tailTrace_1769831 : CollatzResearch.WordTrace tailWord_1769831 prefixEnd_1769831 201949773383904502616267 := by
  unfold tailWord_1769831
  simp only [CollatzResearch.WordTrace]
  refine ⟨64551039651212024915517347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43034026434141349943678231 64551039651212024915517347)
  ·
    refine ⟨96826559476818037373276021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64551039651212024915517347 96826559476818037373276021)
    ·
      refine ⟨9077489950951691003744627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 96826559476818037373276021 9077489950951691003744627)
      ·
        refine ⟨13616234926427536505616941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9077489950951691003744627 13616234926427536505616941)
        ·
          refine ⟨5106088097410326189606353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13616234926427536505616941 5106088097410326189606353)
          ·
            refine ⟨3829566073057744642204765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5106088097410326189606353 3829566073057744642204765)
            ·
              refine ⟨1436087277396654240826787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3829566073057744642204765 1436087277396654240826787)
              ·
                refine ⟨2154130916094981361240181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1436087277396654240826787 2154130916094981361240181)
                ·
                  refine ⟨201949773383904502616267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2154130916094981361240181 201949773383904502616267)
                  ·
                    rfl

theorem cell22_1769831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 1, 5].length) (baseStart_1769831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1769831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1769831 prefixEnd_1769831 := by exact prefixLift 1769831
  have htrace : WordTrace (prefixWord ++ tailWord_1769831) baseStart_1769831 baseEnd_1769831 := by
    simpa [prefixWord, tailWord_1769831, baseEnd_1769831] using wordTrace_append hprefix tailTrace_1769831
  have hstable : (prefixWord ++ tailWord_1769831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769831).length < 2 ^ (prefixWord ++ tailWord_1769831).sum := by decide
  have hdescent : baseEnd_1769831 < baseStart_1769831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769891 : List Nat := [1, 1, 1, 4, 1, 5, 1, 3, 2, 3]
def baseStart_1769891 : Nat := 118140960795 + 1769891 * 2 ^ 59
def prefixEnd_1769891 : Nat := 4983230072969 + 3 ^ 40 * 1769891 * 2
def baseEnd_1769891 : Nat := 605869859377893351348617

theorem tailTrace_1769891 : CollatzResearch.WordTrace tailWord_1769891 prefixEnd_1769891 605869859377893351348617 := by
  unfold tailWord_1769891
  simp only [CollatzResearch.WordTrace]
  refine ⟨64553228030994655162701527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43035485353996436775134351 64553228030994655162701527)
  ·
    refine ⟨96829842046491982744052291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64553228030994655162701527 96829842046491982744052291)
    ·
      refine ⟨145244763069737974116078437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96829842046491982744052291 145244763069737974116078437)
      ·
        refine ⟨27233393075575870146764707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145244763069737974116078437 27233393075575870146764707)
        ·
          refine ⟨40850089613363805220147061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27233393075575870146764707 40850089613363805220147061)
          ·
            refine ⟨3829695901252856739388787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40850089613363805220147061 3829695901252856739388787)
            ·
              refine ⟨5744543851879285109083181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3829695901252856739388787 5744543851879285109083181)
              ·
                refine ⟨2154203944454731915906193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5744543851879285109083181 2154203944454731915906193)
                ·
                  refine ⟨1615652958341048936929645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2154203944454731915906193 1615652958341048936929645)
                  ·
                    refine ⟨605869859377893351348617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1615652958341048936929645 605869859377893351348617)
                    ·
                      rfl

theorem cell22_1769891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 3, 2, 3].length) (baseStart_1769891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1769891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1769891 prefixEnd_1769891 := by exact prefixLift 1769891
  have htrace : WordTrace (prefixWord ++ tailWord_1769891) baseStart_1769891 baseEnd_1769891 := by
    simpa [prefixWord, tailWord_1769891, baseEnd_1769891] using wordTrace_append hprefix tailTrace_1769891
  have hstable : (prefixWord ++ tailWord_1769891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769891).length < 2 ^ (prefixWord ++ tailWord_1769891).sum := by decide
  have hdescent : baseEnd_1769891 < baseStart_1769891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769921 : List Nat := [1, 2, 7, 1, 11]
def baseStart_1769921 : Nat := 118140960795 + 1769921 * 2 ^ 59
def prefixEnd_1769921 : Nat := 4983230072969 + 3 ^ 40 * 1769921 * 2
def baseEnd_1769921 : Nat := 2493333864160424992175

theorem tailTrace_1769921 : CollatzResearch.WordTrace tailWord_1769921 prefixEnd_1769921 2493333864160424992175 := by
  unfold tailWord_1769921
  simp only [CollatzResearch.WordTrace]
  refine ⟨64554322220885970286293617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43036214813923980190862411 64554322220885970286293617)
  ·
    refine ⟨48415741665664477714720213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64554322220885970286293617 48415741665664477714720213)
    ·
      refine ⟨1134743945289011196438755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 48415741665664477714720213 1134743945289011196438755)
      ·
        refine ⟨1702115917933516794658133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1134743945289011196438755 1702115917933516794658133)
        ·
          refine ⟨2493333864160424992175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1702115917933516794658133 2493333864160424992175)
          ·
            rfl

theorem cell22_1769921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 11].length) (baseStart_1769921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1769921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1769921 prefixEnd_1769921 := by exact prefixLift 1769921
  have htrace : WordTrace (prefixWord ++ tailWord_1769921) baseStart_1769921 baseEnd_1769921 := by
    simpa [prefixWord, tailWord_1769921, baseEnd_1769921] using wordTrace_append hprefix tailTrace_1769921
  have hstable : (prefixWord ++ tailWord_1769921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769921).length < 2 ^ (prefixWord ++ tailWord_1769921).sum := by decide
  have hdescent : baseEnd_1769921 < baseStart_1769921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769938 : List Nat := [3, 2, 2, 4, 1, 2, 1, 7]
def baseStart_1769938 : Nat := 118140960795 + 1769938 * 2 ^ 59
def prefixEnd_1769938 : Nat := 4983230072969 + 3 ^ 40 * 1769938 * 2
def baseEnd_1769938 : Nat := 67320660937600099491497

theorem tailTrace_1769938 : CollatzResearch.WordTrace tailWord_1769938 prefixEnd_1769938 67320660937600099491497 := by
  unfold tailWord_1769938
  simp only [CollatzResearch.WordTrace]
  refine ⟨16138735565456095547415617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43036628174549588126441645 16138735565456095547415617)
  ·
    refine ⟨12104051674092071660561713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16138735565456095547415617 12104051674092071660561713)
    ·
      refine ⟨9078038755569053745421285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12104051674092071660561713 9078038755569053745421285)
      ·
        refine ⟨1702132266669197577266491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9078038755569053745421285 1702132266669197577266491)
        ·
          refine ⟨2553198400003796365899737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1702132266669197577266491 2553198400003796365899737)
          ·
            refine ⟨1914898800002847274424803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2553198400003796365899737 1914898800002847274424803)
            ·
              refine ⟨2872348200004270911637205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1914898800002847274424803 2872348200004270911637205)
              ·
                refine ⟨67320660937600099491497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2872348200004270911637205 67320660937600099491497)
                ·
                  rfl

theorem cell22_1769938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 7].length) (baseStart_1769938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1769938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1769938 prefixEnd_1769938 := by exact prefixLift 1769938
  have htrace : WordTrace (prefixWord ++ tailWord_1769938) baseStart_1769938 baseEnd_1769938 := by
    simpa [prefixWord, tailWord_1769938, baseEnd_1769938] using wordTrace_append hprefix tailTrace_1769938
  have hstable : (prefixWord ++ tailWord_1769938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769938).length < 2 ^ (prefixWord ++ tailWord_1769938).sum := by decide
  have hdescent : baseEnd_1769938 < baseStart_1769938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770013 : List Nat := [1, 4, 2, 2, 1, 3, 2, 2, 1, 4]
def baseStart_1770013 : Nat := 118140960795 + 1770013 * 2 ^ 59
def prefixEnd_1770013 : Nat := 4983230072969 + 3 ^ 40 * 1770013 * 2
def baseEnd_1770013 : Nat := 605911622471125699798243

theorem tailTrace_1770013 : CollatzResearch.WordTrace tailWord_1770013 prefixEnd_1770013 605911622471125699798243 := by
  unfold tailWord_1770013
  simp only [CollatzResearch.WordTrace]
  refine ⟨64557677736552669998642693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43038451824368446665761795 64557677736552669998642693)
  ·
    refine ⟨12104564575603625624745505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64557677736552669998642693 12104564575603625624745505)
    ·
      refine ⟨9078423431702719218559129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12104564575603625624745505 9078423431702719218559129)
      ·
        refine ⟨6808817573777039413919347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9078423431702719218559129 6808817573777039413919347)
        ·
          refine ⟨10213226360665559120879021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6808817573777039413919347 10213226360665559120879021)
          ·
            refine ⟨3829959885249584670329633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10213226360665559120879021 3829959885249584670329633)
            ·
              refine ⟨2872469913937188502747225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3829959885249584670329633 2872469913937188502747225)
              ·
                refine ⟨2154352435452891377060419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2872469913937188502747225 2154352435452891377060419)
                ·
                  refine ⟨3231528653179337065590629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2154352435452891377060419 3231528653179337065590629)
                  ·
                    refine ⟨605911622471125699798243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3231528653179337065590629 605911622471125699798243)
                    ·
                      rfl

theorem cell22_1770013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_1770013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1770013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1770013 prefixEnd_1770013 := by exact prefixLift 1770013
  have htrace : WordTrace (prefixWord ++ tailWord_1770013) baseStart_1770013 baseEnd_1770013 := by
    simpa [prefixWord, tailWord_1770013, baseEnd_1770013] using wordTrace_append hprefix tailTrace_1770013
  have hstable : (prefixWord ++ tailWord_1770013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770013).length < 2 ^ (prefixWord ++ tailWord_1770013).sum := by decide
  have hdescent : baseEnd_1770013 < baseStart_1770013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770041 : List Nat := [1, 2, 1, 5, 1, 1, 3, 2, 2, 4]
def baseStart_1770041 : Nat := 118140960795 + 1770041 * 2 ^ 59
def prefixEnd_1770041 : Nat := 4983230072969 + 3 ^ 40 * 1770041 * 2
def baseEnd_1770041 : Nat := 605921207443342960098157

theorem tailTrace_1770041 : CollatzResearch.WordTrace tailWord_1770041 prefixEnd_1770041 605921207443342960098157 := by
  unfold tailWord_1770041
  simp only [CollatzResearch.WordTrace]
  refine ⟨64558698980451230780661977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43039132653634153853774651 64558698980451230780661977)
  ·
    refine ⟨48419024235338423085496483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64558698980451230780661977 48419024235338423085496483)
    ·
      refine ⟨72628536353007634628244725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48419024235338423085496483 72628536353007634628244725)
      ·
        refine ⟨6808925283094465746397943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72628536353007634628244725 6808925283094465746397943)
        ·
          refine ⟨10213387924641698619596915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6808925283094465746397943 10213387924641698619596915)
          ·
            refine ⟨15320081886962547929395373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10213387924641698619596915 15320081886962547929395373)
            ·
              refine ⟨5745030707610955473523265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15320081886962547929395373 5745030707610955473523265)
              ·
                refine ⟨4308773030708216605142449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5745030707610955473523265 4308773030708216605142449)
                ·
                  refine ⟨3231579773031162453856837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4308773030708216605142449 3231579773031162453856837)
                  ·
                    refine ⟨605921207443342960098157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3231579773031162453856837 605921207443342960098157)
                    ·
                      rfl

theorem cell22_1770041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2, 2, 4].length) (baseStart_1770041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1770041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1770041 prefixEnd_1770041 := by exact prefixLift 1770041
  have htrace : WordTrace (prefixWord ++ tailWord_1770041) baseStart_1770041 baseEnd_1770041 := by
    simpa [prefixWord, tailWord_1770041, baseEnd_1770041] using wordTrace_append hprefix tailTrace_1770041
  have hstable : (prefixWord ++ tailWord_1770041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770041).length < 2 ^ (prefixWord ++ tailWord_1770041).sum := by decide
  have hdescent : baseEnd_1770041 < baseStart_1770041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770045 : List Nat := [1, 4, 1, 3, 2, 2, 3, 2, 4]
def baseStart_1770045 : Nat := 118140960795 + 1770045 * 2 ^ 59
def prefixEnd_1770045 : Nat := 4983230072969 + 3 ^ 40 * 1770045 * 2
def baseEnd_1770045 : Nat := 201974192241696094332715

theorem tailTrace_1770045 : CollatzResearch.WordTrace tailWord_1770045 prefixEnd_1770045 201974192241696094332715 := by
  unfold tailWord_1770045
  simp only [CollatzResearch.WordTrace]
  refine ⟨64558844872436739463807589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43039229914957826309205059 64558844872436739463807589)
  ·
    refine ⟨12104783413581888649463923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64558844872436739463807589 12104783413581888649463923)
    ·
      refine ⟨18157175120372832974195885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12104783413581888649463923 18157175120372832974195885)
      ·
        refine ⟨6808940670139812365323457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18157175120372832974195885 6808940670139812365323457)
        ·
          refine ⟨5106705502604859273992593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6808940670139812365323457 5106705502604859273992593)
          ·
            refine ⟨3830029126953644455494445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5106705502604859273992593 3830029126953644455494445)
            ·
              refine ⟨1436260922607616670810417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3830029126953644455494445 1436260922607616670810417)
              ·
                refine ⟨1077195691955712503107813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1436260922607616670810417 1077195691955712503107813)
                ·
                  refine ⟨201974192241696094332715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1077195691955712503107813 201974192241696094332715)
                  ·
                    rfl

theorem cell22_1770045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 2, 4].length) (baseStart_1770045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1770045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1770045 prefixEnd_1770045 := by exact prefixLift 1770045
  have htrace : WordTrace (prefixWord ++ tailWord_1770045) baseStart_1770045 baseEnd_1770045 := by
    simpa [prefixWord, tailWord_1770045, baseEnd_1770045] using wordTrace_append hprefix tailTrace_1770045
  have hstable : (prefixWord ++ tailWord_1770045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770045).length < 2 ^ (prefixWord ++ tailWord_1770045).sum := by decide
  have hdescent : baseEnd_1770045 < baseStart_1770045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770071 : List Nat := [1, 1, 3, 2, 2, 2, 2, 1, 5, 3]
def baseStart_1770071 : Nat := 118140960795 + 1770071 * 2 ^ 59
def prefixEnd_1770071 : Nat := 4983230072969 + 3 ^ 40 * 1770071 * 2
def baseEnd_1770071 : Nat := 605931477056432881848065

theorem tailTrace_1770071 : CollatzResearch.WordTrace tailWord_1770071 prefixEnd_1770071 605931477056432881848065 := by
  unfold tailWord_1770071
  simp only [CollatzResearch.WordTrace]
  refine ⟨64559793170342545904254067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43039862113561697269502711 64559793170342545904254067)
  ·
    refine ⟨96839689755513818856381101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64559793170342545904254067 96839689755513818856381101)
    ·
      refine ⟨36314883658317682071142913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96839689755513818856381101 36314883658317682071142913)
      ·
        refine ⟨27236162743738261553357185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36314883658317682071142913 27236162743738261553357185)
        ·
          refine ⟨20427122057803696165017889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27236162743738261553357185 20427122057803696165017889)
          ·
            refine ⟨15320341543352772123763417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20427122057803696165017889 15320341543352772123763417)
            ·
              refine ⟨11490256157514579092822563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15320341543352772123763417 11490256157514579092822563)
              ·
                refine ⟨17235384236271868639233845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11490256157514579092822563 17235384236271868639233845)
                ·
                  refine ⟨1615817272150487684928173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17235384236271868639233845 1615817272150487684928173)
                  ·
                    refine ⟨605931477056432881848065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1615817272150487684928173 605931477056432881848065)
                    ·
                      rfl

theorem cell22_1770071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 5, 3].length) (baseStart_1770071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1770071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1770071 prefixEnd_1770071 := by exact prefixLift 1770071
  have htrace : WordTrace (prefixWord ++ tailWord_1770071) baseStart_1770071 baseEnd_1770071 := by
    simpa [prefixWord, tailWord_1770071, baseEnd_1770071] using wordTrace_append hprefix tailTrace_1770071
  have hstable : (prefixWord ++ tailWord_1770071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770071).length < 2 ^ (prefixWord ++ tailWord_1770071).sum := by decide
  have hdescent : baseEnd_1770071 < baseStart_1770071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770105 : List Nat := [1, 2, 1, 3, 3, 3, 1, 4, 1, 3]
def baseStart_1770105 : Nat := 118140960795 + 1770105 * 2 ^ 59
def prefixEnd_1770105 : Nat := 4983230072969 + 3 ^ 40 * 1770105 * 2
def baseEnd_1770105 : Nat := 605943115951268126497961

theorem tailTrace_1770105 : CollatzResearch.WordTrace tailWord_1770105 prefixEnd_1770105 605943115951268126497961 := by
  unfold tailWord_1770105
  simp only [CollatzResearch.WordTrace]
  refine ⟨64561033252219369710991769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43040688834812913140661179 64561033252219369710991769)
  ·
    refine ⟨48420774939164527283243827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64561033252219369710991769 48420774939164527283243827)
    ·
      refine ⟨72631162408746790924865741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48420774939164527283243827 72631162408746790924865741)
      ·
        refine ⟨27236685903280046596824653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72631162408746790924865741 27236685903280046596824653)
        ·
          refine ⟨10213757213730017473809245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27236685903280046596824653 10213757213730017473809245)
          ·
            refine ⟨3830158955148756552678467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10213757213730017473809245 3830158955148756552678467)
            ·
              refine ⟨5745238432723134829017701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3830158955148756552678467 5745238432723134829017701)
              ·
                refine ⟨1077232206135587780440819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5745238432723134829017701 1077232206135587780440819)
                ·
                  refine ⟨1615848309203381670661229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1077232206135587780440819 1615848309203381670661229)
                  ·
                    refine ⟨605943115951268126497961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1615848309203381670661229 605943115951268126497961)
                    ·
                      rfl

theorem cell22_1770105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 4, 1, 3].length) (baseStart_1770105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1770105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1770105 prefixEnd_1770105 := by exact prefixLift 1770105
  have htrace : WordTrace (prefixWord ++ tailWord_1770105) baseStart_1770105 baseEnd_1770105 := by
    simpa [prefixWord, tailWord_1770105, baseEnd_1770105] using wordTrace_append hprefix tailTrace_1770105
  have hstable : (prefixWord ++ tailWord_1770105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770105).length < 2 ^ (prefixWord ++ tailWord_1770105).sum := by decide
  have hdescent : baseEnd_1770105 < baseStart_1770105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770116 : List Nat := [2, 3, 2, 1, 3, 1, 1, 1, 1, 7]
def baseStart_1770116 : Nat := 118140960795 + 1770116 * 2 ^ 59
def prefixEnd_1770116 : Nat := 4983230072969 + 3 ^ 40 * 1770116 * 2
def baseEnd_1770116 : Nat := 605946881476067764472927

theorem tailTrace_1770116 : CollatzResearch.WordTrace tailWord_1770116 prefixEnd_1770116 605946881476067764472927 := by
  unfold tailWord_1770116
  simp only [CollatzResearch.WordTrace]
  refine ⟨32280717227589759294821101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43040956303453012393094801 32280717227589759294821101)
  ·
    refine ⟨12105268960346159735557913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32280717227589759294821101 12105268960346159735557913)
    ·
      refine ⟨9078951720259619801668435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12105268960346159735557913 9078951720259619801668435)
      ·
        refine ⟨13618427580389429702502653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9078951720259619801668435 13618427580389429702502653)
        ·
          refine ⟨5106910342646036138438495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13618427580389429702502653 5106910342646036138438495)
          ·
            refine ⟨7660365513969054207657743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5106910342646036138438495 7660365513969054207657743)
            ·
              refine ⟨11490548270953581311486615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7660365513969054207657743 11490548270953581311486615)
              ·
                refine ⟨17235822406430371967229923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11490548270953581311486615 17235822406430371967229923)
                ·
                  refine ⟨25853733609645557950844885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17235822406430371967229923 25853733609645557950844885)
                  ·
                    refine ⟨605946881476067764472927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25853733609645557950844885 605946881476067764472927)
                    ·
                      rfl

theorem cell22_1770116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_1770116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1770116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1770116 prefixEnd_1770116 := by exact prefixLift 1770116
  have htrace : WordTrace (prefixWord ++ tailWord_1770116) baseStart_1770116 baseEnd_1770116 := by
    simpa [prefixWord, tailWord_1770116, baseEnd_1770116] using wordTrace_append hprefix tailTrace_1770116
  have hstable : (prefixWord ++ tailWord_1770116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770116).length < 2 ^ (prefixWord ++ tailWord_1770116).sum := by decide
  have hdescent : baseEnd_1770116 < baseStart_1770116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770148 : List Nat := [2, 3, 1, 2, 2, 1, 3, 3, 1, 4]
def baseStart_1770148 : Nat := 118140960795 + 1770148 * 2 ^ 59
def prefixEnd_1770148 : Nat := 4983230072969 + 3 ^ 40 * 1770148 * 2
def baseEnd_1770148 : Nat := 605957835730030347672829

theorem tailTrace_1770148 : CollatzResearch.WordTrace tailWord_1770148 prefixEnd_1770148 605957835730030347672829 := by
  unfold tailWord_1770148
  simp only [CollatzResearch.WordTrace]
  refine ⟨32281300795531794027403549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43041734394042392036538065 32281300795531794027403549)
  ·
    refine ⟨12105487798324422760276331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32281300795531794027403549 12105487798324422760276331)
    ·
      refine ⟨18158231697486634140414497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12105487798324422760276331 18158231697486634140414497)
      ·
        refine ⟨13618673773114975605310873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18158231697486634140414497 13618673773114975605310873)
        ·
          refine ⟨10214005329836231703983155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13618673773114975605310873 10214005329836231703983155)
          ·
            refine ⟨15321007994754347555974733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10214005329836231703983155 15321007994754347555974733)
            ·
              refine ⟨5745377998032880333490525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15321007994754347555974733 5745377998032880333490525)
              ·
                refine ⟨2154516749262330125058947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5745377998032880333490525 2154516749262330125058947)
                ·
                  refine ⟨3231775123893495187588421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2154516749262330125058947 3231775123893495187588421)
                  ·
                    refine ⟨605957835730030347672829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3231775123893495187588421 605957835730030347672829)
                    ·
                      rfl

theorem cell22_1770148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 3, 1, 4].length) (baseStart_1770148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1770148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1770148 prefixEnd_1770148 := by exact prefixLift 1770148
  have htrace : WordTrace (prefixWord ++ tailWord_1770148) baseStart_1770148 baseEnd_1770148 := by
    simpa [prefixWord, tailWord_1770148, baseEnd_1770148] using wordTrace_append hprefix tailTrace_1770148
  have hstable : (prefixWord ++ tailWord_1770148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770148).length < 2 ^ (prefixWord ++ tailWord_1770148).sum := by decide
  have hdescent : baseEnd_1770148 < baseStart_1770148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770163 : List Nat := [1, 1, 1, 2, 3, 4, 2, 4, 4]
def baseStart_1770163 : Nat := 118140960795 + 1770163 * 2 ^ 59
def prefixEnd_1770163 : Nat := 4983230072969 + 3 ^ 40 * 1770163 * 2
def baseEnd_1770163 : Nat := 201987656845525102849261

theorem tailTrace_1770163 : CollatzResearch.WordTrace tailWord_1770163 prefixEnd_1770163 201987656845525102849261 := by
  unfold tailWord_1770163
  simp only [CollatzResearch.WordTrace]
  refine ⟨64563148686009245616603143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43042099124006163744402095 64563148686009245616603143)
  ·
    refine ⟨96844723029013868424904715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64563148686009245616603143 96844723029013868424904715)
    ·
      refine ⟨145267084543520802637357073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96844723029013868424904715 145267084543520802637357073)
      ·
        refine ⟨108950313407640601978017805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145267084543520802637357073 108950313407640601978017805)
        ·
          refine ⟨40856367527865225741756677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108950313407640601978017805 40856367527865225741756677)
          ·
            refine ⟨7660568911474729826579377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40856367527865225741756677 7660568911474729826579377)
            ·
              refine ⟨5745426683606047369934533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7660568911474729826579377 5745426683606047369934533)
              ·
                refine ⟨1077267503176133881862725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5745426683606047369934533 1077267503176133881862725)
                ·
                  refine ⟨201987656845525102849261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1077267503176133881862725 201987656845525102849261)
                  ·
                    rfl

theorem cell22_1770163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 4, 4].length) (baseStart_1770163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1770163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1770163 prefixEnd_1770163 := by exact prefixLift 1770163
  have htrace : WordTrace (prefixWord ++ tailWord_1770163) baseStart_1770163 baseEnd_1770163 := by
    simpa [prefixWord, tailWord_1770163, baseEnd_1770163] using wordTrace_append hprefix tailTrace_1770163
  have hstable : (prefixWord ++ tailWord_1770163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770163).length < 2 ^ (prefixWord ++ tailWord_1770163).sum := by decide
  have hdescent : baseEnd_1770163 < baseStart_1770163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770176 : List Nat := [2, 1, 1, 2, 4, 2, 1, 2, 1, 6]
def baseStart_1770176 : Nat := 118140960795 + 1770176 * 2 ^ 59
def prefixEnd_1770176 : Nat := 4983230072969 + 3 ^ 40 * 1770176 * 2
def baseEnd_1770176 : Nat := 605967420702247607972743

theorem tailTrace_1770176 : CollatzResearch.WordTrace tailWord_1770176 prefixEnd_1770176 605967420702247607972743 := by
  unfold tailWord_1770176
  simp only [CollatzResearch.WordTrace]
  refine ⟨32281811417481074418413191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43042415223308099224550921 32281811417481074418413191)
  ·
    refine ⟨48422717126221611627619787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32281811417481074418413191 48422717126221611627619787)
    ·
      refine ⟨72634075689332417441429681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48422717126221611627619787 72634075689332417441429681)
      ·
        refine ⟨54475556766999313081072261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72634075689332417441429681 54475556766999313081072261)
        ·
          refine ⟨10214166893812371202701049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54475556766999313081072261 10214166893812371202701049)
          ·
            refine ⟨7660625170359278402025787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10214166893812371202701049 7660625170359278402025787)
            ·
              refine ⟨11490937755538917603038681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7660625170359278402025787 11490937755538917603038681)
              ·
                refine ⟨8618203316654188202279011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11490937755538917603038681 8618203316654188202279011)
                ·
                  refine ⟨12927304974981282303418517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8618203316654188202279011 12927304974981282303418517)
                  ·
                    refine ⟨605967420702247607972743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12927304974981282303418517 605967420702247607972743)
                    ·
                      rfl

theorem cell22_1770176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 1, 6].length) (baseStart_1770176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1770176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1770176 prefixEnd_1770176 := by exact prefixLift 1770176
  have htrace : WordTrace (prefixWord ++ tailWord_1770176) baseStart_1770176 baseEnd_1770176 := by
    simpa [prefixWord, tailWord_1770176, baseEnd_1770176] using wordTrace_append hprefix tailTrace_1770176
  have hstable : (prefixWord ++ tailWord_1770176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770176).length < 2 ^ (prefixWord ++ tailWord_1770176).sum := by decide
  have hdescent : baseEnd_1770176 < baseStart_1770176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770251 : List Nat := [1, 1, 1, 1, 5, 1, 1, 2, 4, 5]
def baseStart_1770251 : Nat := 118140960795 + 1770251 * 2 ^ 59
def prefixEnd_1770251 : Nat := 4983230072969 + 3 ^ 40 * 1770251 * 2
def baseEnd_1770251 : Nat := 605993094734972412347513

theorem tailTrace_1770251 : CollatzResearch.WordTrace tailWord_1770251 prefixEnd_1770251 605993094734972412347513 := by
  unfold tailWord_1770251
  simp only [CollatzResearch.WordTrace]
  refine ⟨64566358309690436645806607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43044238873126957763871071 64566358309690436645806607)
  ·
    refine ⟨96849537464535654968709911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64566358309690436645806607 96849537464535654968709911)
    ·
      refine ⟨145274306196803482453064867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96849537464535654968709911 145274306196803482453064867)
      ·
        refine ⟨217911459295205223679597301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145274306196803482453064867 217911459295205223679597301)
        ·
          refine ⟨20429199308925489719962247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 217911459295205223679597301 20429199308925489719962247)
          ·
            refine ⟨30643798963388234579943371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20429199308925489719962247 30643798963388234579943371)
            ·
              refine ⟨45965698445082351869915057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30643798963388234579943371 45965698445082351869915057)
              ·
                refine ⟨34474273833811763902436293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45965698445082351869915057 34474273833811763902436293)
                ·
                  refine ⟨6463926343839705731706805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34474273833811763902436293 6463926343839705731706805)
                  ·
                    refine ⟨605993094734972412347513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6463926343839705731706805 605993094734972412347513)
                    ·
                      rfl

theorem cell22_1770251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4, 5].length) (baseStart_1770251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1770251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1770251 prefixEnd_1770251 := by exact prefixLift 1770251
  have htrace : WordTrace (prefixWord ++ tailWord_1770251) baseStart_1770251 baseEnd_1770251 := by
    simpa [prefixWord, tailWord_1770251, baseEnd_1770251] using wordTrace_append hprefix tailTrace_1770251
  have hstable : (prefixWord ++ tailWord_1770251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770251).length < 2 ^ (prefixWord ++ tailWord_1770251).sum := by decide
  have hdescent : baseEnd_1770251 < baseStart_1770251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770274 : List Nat := [3, 3, 1, 1, 2, 2, 4, 2, 1, 3]
def baseStart_1770274 : Nat := 118140960795 + 1770274 * 2 ^ 59
def prefixEnd_1770274 : Nat := 4983230072969 + 3 ^ 40 * 1770274 * 2
def baseEnd_1770274 : Nat := 606000968105008019022443

theorem tailTrace_1770274 : CollatzResearch.WordTrace tailWord_1770274 prefixEnd_1770274 606000968105008019022443 := by
  unfold tailWord_1770274
  simp only [CollatzResearch.WordTrace]
  refine ⟨16141799297151777893473469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43044798125738074382595917 16141799297151777893473469)
  ·
    refine ⟨6053174736431916710052551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16141799297151777893473469 6053174736431916710052551)
    ·
      refine ⟨9079762104647875065078827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6053174736431916710052551 9079762104647875065078827)
      ·
        refine ⟨13619643156971812597618241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9079762104647875065078827 13619643156971812597618241)
        ·
          refine ⟨10214732367728859448213681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13619643156971812597618241 10214732367728859448213681)
          ·
            refine ⟨7661049275796644586160261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10214732367728859448213681 7661049275796644586160261)
            ·
              refine ⟨1436446739211870859905049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7661049275796644586160261 1436446739211870859905049)
              ·
                refine ⟨1077335054408903144928787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1436446739211870859905049 1077335054408903144928787)
                ·
                  refine ⟨1616002581613354717393181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1077335054408903144928787 1616002581613354717393181)
                  ·
                    refine ⟨606000968105008019022443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1616002581613354717393181 606000968105008019022443)
                    ·
                      rfl

theorem cell22_1770274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 2, 1, 3].length) (baseStart_1770274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1770274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1770274 prefixEnd_1770274 := by exact prefixLift 1770274
  have htrace : WordTrace (prefixWord ++ tailWord_1770274) baseStart_1770274 baseEnd_1770274 := by
    simpa [prefixWord, tailWord_1770274, baseEnd_1770274] using wordTrace_append hprefix tailTrace_1770274
  have hstable : (prefixWord ++ tailWord_1770274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770274).length < 2 ^ (prefixWord ++ tailWord_1770274).sum := by decide
  have hdescent : baseEnd_1770274 < baseStart_1770274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770313 : List Nat := [1, 2, 1, 1, 2, 5, 2, 2, 1, 5]
def baseStart_1770313 : Nat := 118140960795 + 1770313 * 2 ^ 59
def prefixEnd_1770313 : Nat := 4983230072969 + 3 ^ 40 * 1770313 * 2
def baseEnd_1770313 : Nat := 606014318602024917297323

theorem tailTrace_1770313 : CollatzResearch.WordTrace tailWord_1770313 prefixEnd_1770313 606014318602024917297323 := by
  unfold tailWord_1770313
  simp only [CollatzResearch.WordTrace]
  refine ⟨64568619635465821234563593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43045746423643880823042395 64568619635465821234563593)
  ·
    refine ⟨48426464726599365925922695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64568619635465821234563593 48426464726599365925922695)
    ·
      refine ⟨72639697089899048888884043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48426464726599365925922695 72639697089899048888884043)
      ·
        refine ⟨108959545634848573333326065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72639697089899048888884043 108959545634848573333326065)
        ·
          refine ⟨81719659226136429999994549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108959545634848573333326065 81719659226136429999994549)
          ·
            refine ⟨7661218052450290312499489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81719659226136429999994549 7661218052450290312499489)
            ·
              refine ⟨5745913539337717734374617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7661218052450290312499489 5745913539337717734374617)
              ·
                refine ⟨4309435154503288300780963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5745913539337717734374617 4309435154503288300780963)
                ·
                  refine ⟨6464152731754932451171445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4309435154503288300780963 6464152731754932451171445)
                  ·
                    refine ⟨606014318602024917297323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6464152731754932451171445 606014318602024917297323)
                    ·
                      rfl

theorem cell22_1770313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2, 1, 5].length) (baseStart_1770313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1770313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1770313 prefixEnd_1770313 := by exact prefixLift 1770313
  have htrace : WordTrace (prefixWord ++ tailWord_1770313) baseStart_1770313 baseEnd_1770313 := by
    simpa [prefixWord, tailWord_1770313, baseEnd_1770313] using wordTrace_append hprefix tailTrace_1770313
  have hstable : (prefixWord ++ tailWord_1770313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770313).length < 2 ^ (prefixWord ++ tailWord_1770313).sum := by decide
  have hdescent : baseEnd_1770313 < baseStart_1770313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770328 : List Nat := [2, 1, 2, 2, 1, 1, 1, 6, 2, 4]
def baseStart_1770328 : Nat := 118140960795 + 1770328 * 2 ^ 59
def prefixEnd_1770328 : Nat := 4983230072969 + 3 ^ 40 * 1770328 * 2
def baseEnd_1770328 : Nat := 606019453408569878172277

theorem tailTrace_1770328 : CollatzResearch.WordTrace tailWord_1770328 prefixEnd_1770328 606019453408569878172277 := by
  unfold tailWord_1770328
  simp only [CollatzResearch.WordTrace]
  refine ⟨32284583365205739398179819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43046111153607652530906425 32284583365205739398179819)
  ·
    refine ⟨48426875047808609097269729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32284583365205739398179819 48426875047808609097269729)
    ·
      refine ⟨36320156285856456822952297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48426875047808609097269729 36320156285856456822952297)
      ·
        refine ⟨27240117214392342617214223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36320156285856456822952297 27240117214392342617214223)
        ·
          refine ⟨40860175821588513925821335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27240117214392342617214223 40860175821588513925821335)
          ·
            refine ⟨61290263732382770888732003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40860175821588513925821335 61290263732382770888732003)
            ·
              refine ⟨91935395598574156333098005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61290263732382770888732003 91935395598574156333098005)
              ·
                refine ⟨4309471668683163578113969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 91935395598574156333098005 4309471668683163578113969)
                ·
                  refine ⟨3232103751512372683585477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4309471668683163578113969 3232103751512372683585477)
                  ·
                    refine ⟨606019453408569878172277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3232103751512372683585477 606019453408569878172277)
                    ·
                      rfl

theorem cell22_1770328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6, 2, 4].length) (baseStart_1770328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1770328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1770328 prefixEnd_1770328 := by exact prefixLift 1770328
  have htrace : WordTrace (prefixWord ++ tailWord_1770328) baseStart_1770328 baseEnd_1770328 := by
    simpa [prefixWord, tailWord_1770328, baseEnd_1770328] using wordTrace_append hprefix tailTrace_1770328
  have hstable : (prefixWord ++ tailWord_1770328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770328).length < 2 ^ (prefixWord ++ tailWord_1770328).sum := by decide
  have hdescent : baseEnd_1770328 < baseStart_1770328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770330 : List Nat := [3, 1, 1, 2, 1, 5, 1, 1, 4, 3]
def baseStart_1770330 : Nat := 118140960795 + 1770330 * 2 ^ 59
def prefixEnd_1770330 : Nat := 4983230072969 + 3 ^ 40 * 1770330 * 2
def baseEnd_1770330 : Nat := 606020138049442539622271

theorem tailTrace_1770330 : CollatzResearch.WordTrace tailWord_1770330 prefixEnd_1770330 606020138049442539622271 := by
  unfold tailWord_1770330
  simp only [CollatzResearch.WordTrace]
  refine ⟨16142309919101058284483111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43046159784269488758621629 16142309919101058284483111)
  ·
    refine ⟨24213464878651587426724667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16142309919101058284483111 24213464878651587426724667)
    ·
      refine ⟨36320197317977381140087001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24213464878651587426724667 36320197317977381140087001)
      ·
        refine ⟨27240147988483035855065251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36320197317977381140087001 27240147988483035855065251)
        ·
          refine ⟨40860221982724553782597877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27240147988483035855065251 40860221982724553782597877)
          ·
            refine ⟨3830645810880426917118551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40860221982724553782597877 3830645810880426917118551)
            ·
              refine ⟨5745968716320640375677827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3830645810880426917118551 5745968716320640375677827)
              ·
                refine ⟨8618953074480960563516741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5745968716320640375677827 8618953074480960563516741)
                ·
                  refine ⟨1616053701465180105659389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8618953074480960563516741 1616053701465180105659389)
                  ·
                    refine ⟨606020138049442539622271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1616053701465180105659389 606020138049442539622271)
                    ·
                      rfl

theorem cell22_1770330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 4, 3].length) (baseStart_1770330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1770330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1770330 prefixEnd_1770330 := by exact prefixLift 1770330
  have htrace : WordTrace (prefixWord ++ tailWord_1770330) baseStart_1770330 baseEnd_1770330 := by
    simpa [prefixWord, tailWord_1770330, baseEnd_1770330] using wordTrace_append hprefix tailTrace_1770330
  have hstable : (prefixWord ++ tailWord_1770330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770330).length < 2 ^ (prefixWord ++ tailWord_1770330).sum := by decide
  have hdescent : baseEnd_1770330 < baseStart_1770330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770332 : List Nat := [2, 2, 4, 2, 1, 1, 2, 4, 4]
def baseStart_1770332 : Nat := 118140960795 + 1770332 * 2 ^ 59
def prefixEnd_1770332 : Nat := 4983230072969 + 3 ^ 40 * 1770332 * 2
def baseEnd_1770332 : Nat := 202006940896771733690755

theorem tailTrace_1770332 : CollatzResearch.WordTrace tailWord_1770332 prefixEnd_1770332 202006940896771733690755 := by
  unfold tailWord_1770332
  simp only [CollatzResearch.WordTrace]
  refine ⟨32284656311198493739752625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43046208414931324986336833 32284656311198493739752625)
  ·
    refine ⟨24213492233398870304814469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32284656311198493739752625 24213492233398870304814469)
    ·
      refine ⟨4540029793762288182152713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24213492233398870304814469 4540029793762288182152713)
      ·
        refine ⟨3405022345321716136614535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4540029793762288182152713 3405022345321716136614535)
        ·
          refine ⟨5107533517982574204921803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3405022345321716136614535 5107533517982574204921803)
          ·
            refine ⟨7661300276973861307382705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5107533517982574204921803 7661300276973861307382705)
            ·
              refine ⟨5745975207730395980537029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7661300276973861307382705 5745975207730395980537029)
              ·
                refine ⟨1077370351449449246350693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5745975207730395980537029 1077370351449449246350693)
                ·
                  refine ⟨202006940896771733690755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1077370351449449246350693 202006940896771733690755)
                  ·
                    rfl

theorem cell22_1770332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 4, 4].length) (baseStart_1770332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1770332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1770332 prefixEnd_1770332 := by exact prefixLift 1770332
  have htrace : WordTrace (prefixWord ++ tailWord_1770332) baseStart_1770332 baseEnd_1770332 := by
    simpa [prefixWord, tailWord_1770332, baseEnd_1770332] using wordTrace_append hprefix tailTrace_1770332
  have hstable : (prefixWord ++ tailWord_1770332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770332).length < 2 ^ (prefixWord ++ tailWord_1770332).sum := by decide
  have hdescent : baseEnd_1770332 < baseStart_1770332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770366 : List Nat := [4, 2, 3, 1, 2, 2, 1, 3, 4]
def baseStart_1770366 : Nat := 118140960795 + 1770366 * 2 ^ 59
def prefixEnd_1770366 : Nat := 4983230072969 + 3 ^ 40 * 1770366 * 2
def baseEnd_1770366 : Nat := 202010820528383481907387

theorem tailTrace_1770366 : CollatzResearch.WordTrace tailWord_1770366 prefixEnd_1770366 202010820528383481907387 := by
  unfold tailWord_1770366
  simp only [CollatzResearch.WordTrace]
  refine ⟨8071319088034226410780369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43047035136182540857495301 8071319088034226410780369)
  ·
    refine ⟨6053489316025669808085277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8071319088034226410780369 6053489316025669808085277)
    ·
      refine ⟨2270058493509626178031979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6053489316025669808085277 2270058493509626178031979)
      ·
        refine ⟨3405087740264439267047969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2270058493509626178031979 3405087740264439267047969)
        ·
          refine ⟨2553815805198329450285977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3405087740264439267047969 2553815805198329450285977)
          ·
            refine ⟨1915361853898747087714483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2553815805198329450285977 1915361853898747087714483)
            ·
              refine ⟨2873042780848120631571725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1915361853898747087714483 2873042780848120631571725)
              ·
                refine ⟨1077391042818045236839397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2873042780848120631571725 1077391042818045236839397)
                ·
                  refine ⟨202010820528383481907387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1077391042818045236839397 202010820528383481907387)
                  ·
                    rfl

theorem cell22_1770366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_1770366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1770366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1770366 prefixEnd_1770366 := by exact prefixLift 1770366
  have htrace : WordTrace (prefixWord ++ tailWord_1770366) baseStart_1770366 baseEnd_1770366 := by
    simpa [prefixWord, tailWord_1770366, baseEnd_1770366] using wordTrace_append hprefix tailTrace_1770366
  have hstable : (prefixWord ++ tailWord_1770366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770366).length < 2 ^ (prefixWord ++ tailWord_1770366).sum := by decide
  have hdescent : baseEnd_1770366 < baseStart_1770366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770403 : List Nat := [1, 1, 1, 4, 1, 2, 2, 3, 2, 5]
def baseStart_1770403 : Nat := 118140960795 + 1770403 * 2 ^ 59
def prefixEnd_1770403 : Nat := 4983230072969 + 3 ^ 40 * 1770403 * 2
def baseEnd_1770403 : Nat := 606045127441294682547047

theorem tailTrace_1770403 : CollatzResearch.WordTrace tailWord_1770403 prefixEnd_1770403 606045127441294682547047 := by
  unfold tailWord_1770403
  simp only [CollatzResearch.WordTrace]
  refine ⟨64571902205139766605339863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43047934803426511070226575 64571902205139766605339863)
  ·
    refine ⟨96857853307709649908009795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64571902205139766605339863 96857853307709649908009795)
    ·
      refine ⟨145286779961564474862014693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96857853307709649908009795 145286779961564474862014693)
      ·
        refine ⟨27241271242793339036627755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145286779961564474862014693 27241271242793339036627755)
        ·
          refine ⟨40861906864190008554941633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27241271242793339036627755 40861906864190008554941633)
          ·
            refine ⟨30646430148142506416206225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40861906864190008554941633 30646430148142506416206225)
            ·
              refine ⟨22984822611106879812154669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30646430148142506416206225 22984822611106879812154669)
              ·
                refine ⟨8619308479165079929558001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22984822611106879812154669 8619308479165079929558001)
                ·
                  refine ⟨6464481359373809947168501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8619308479165079929558001 6464481359373809947168501)
                  ·
                    refine ⟨606045127441294682547047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6464481359373809947168501 606045127441294682547047)
                    ·
                      rfl

theorem cell22_1770403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2, 5].length) (baseStart_1770403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1770403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1770403 prefixEnd_1770403 := by exact prefixLift 1770403
  have htrace : WordTrace (prefixWord ++ tailWord_1770403) baseStart_1770403 baseEnd_1770403 := by
    simpa [prefixWord, tailWord_1770403, baseEnd_1770403] using wordTrace_append hprefix tailTrace_1770403
  have hstable : (prefixWord ++ tailWord_1770403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770403).length < 2 ^ (prefixWord ++ tailWord_1770403).sum := by decide
  have hdescent : baseEnd_1770403 < baseStart_1770403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770448 : List Nat := [2, 1, 1, 1, 1, 2, 3, 1, 5, 5]
def baseStart_1770448 : Nat := 118140960795 + 1770448 * 2 ^ 59
def prefixEnd_1770448 : Nat := 4983230072969 + 3 ^ 40 * 1770448 * 2
def baseEnd_1770448 : Nat := 606060531860929565171909

theorem tailTrace_1770448 : CollatzResearch.WordTrace tailWord_1770448 prefixEnd_1770448 606060531860929565171909 := by
  unfold tailWord_1770448
  simp only [CollatzResearch.WordTrace]
  refine ⟨32286771744988369645363999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43049028993317826193818665 32286771744988369645363999)
  ·
    refine ⟨48430157617482554468045999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32286771744988369645363999 48430157617482554468045999)
    ·
      refine ⟨72645236426223831702068999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48430157617482554468045999 72645236426223831702068999)
      ·
        refine ⟨108967854639335747553103499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72645236426223831702068999 108967854639335747553103499)
        ·
          refine ⟨163451781959003621329655249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108967854639335747553103499 163451781959003621329655249)
          ·
            refine ⟨122588836469252715997241437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163451781959003621329655249 122588836469252715997241437)
            ·
              refine ⟨45970813675969768498965539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122588836469252715997241437 45970813675969768498965539)
              ·
                refine ⟨68956220513954652748448309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45970813675969768498965539 68956220513954652748448309)
                ·
                  refine ⟨6464645673183248695167029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68956220513954652748448309 6464645673183248695167029)
                  ·
                    refine ⟨606060531860929565171909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6464645673183248695167029 606060531860929565171909)
                    ·
                      rfl

theorem cell22_1770448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 5, 5].length) (baseStart_1770448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1770448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1770448 prefixEnd_1770448 := by exact prefixLift 1770448
  have htrace : WordTrace (prefixWord ++ tailWord_1770448) baseStart_1770448 baseEnd_1770448 := by
    simpa [prefixWord, tailWord_1770448, baseEnd_1770448] using wordTrace_append hprefix tailTrace_1770448
  have hstable : (prefixWord ++ tailWord_1770448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770448).length < 2 ^ (prefixWord ++ tailWord_1770448).sum := by decide
  have hdescent : baseEnd_1770448 < baseStart_1770448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770465 : List Nat := [1, 2, 3, 1, 2, 1, 1, 2, 6, 3]
def baseStart_1770465 : Nat := 118140960795 + 1770465 * 2 ^ 59
def prefixEnd_1770465 : Nat := 4983230072969 + 3 ^ 40 * 1770465 * 2
def baseEnd_1770465 : Nat := 606066351308347187496857

theorem tailTrace_1770465 : CollatzResearch.WordTrace tailWord_1770465 prefixEnd_1770465 606066351308347187496857 := by
  unfold tailWord_1770465
  simp only [CollatzResearch.WordTrace]
  refine ⟨64574163530915151194096849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43049442353943434129397899 64574163530915151194096849)
  ·
    refine ⟨48430622648186363395572637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64574163530915151194096849 48430622648186363395572637)
    ·
      refine ⟨18161483493069886273339739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48430622648186363395572637 18161483493069886273339739)
      ·
        refine ⟨27242225239604829410009609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18161483493069886273339739 27242225239604829410009609)
        ·
          refine ⟨20431668929703622057507207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27242225239604829410009609 20431668929703622057507207)
          ·
            refine ⟨30647503394555433086260811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20431668929703622057507207 30647503394555433086260811)
            ·
              refine ⟨45971255091833149629391217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30647503394555433086260811 45971255091833149629391217)
              ·
                refine ⟨34478441318874862222043413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45971255091833149629391217 34478441318874862222043413)
                ·
                  refine ⟨1616176936822259166658285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 34478441318874862222043413 1616176936822259166658285)
                  ·
                    refine ⟨606066351308347187496857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1616176936822259166658285 606066351308347187496857)
                    ·
                      rfl

theorem cell22_1770465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 6, 3].length) (baseStart_1770465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1770465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1770465 prefixEnd_1770465 := by exact prefixLift 1770465
  have htrace : WordTrace (prefixWord ++ tailWord_1770465) baseStart_1770465 baseEnd_1770465 := by
    simpa [prefixWord, tailWord_1770465, baseEnd_1770465] using wordTrace_append hprefix tailTrace_1770465
  have hstable : (prefixWord ++ tailWord_1770465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770465).length < 2 ^ (prefixWord ++ tailWord_1770465).sum := by decide
  have hdescent : baseEnd_1770465 < baseStart_1770465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770486 : List Nat := [5, 1, 1, 1, 3, 3, 2, 1, 1, 4]
def baseStart_1770486 : Nat := 118140960795 + 1770486 * 2 ^ 59
def prefixEnd_1770486 : Nat := 4983230072969 + 3 ^ 40 * 1770486 * 2
def baseEnd_1770486 : Nat := 606073540037510132721793

theorem tailTrace_1770486 : CollatzResearch.WordTrace tailWord_1770486 prefixEnd_1770486 606073540037510132721793 := by
  unfold tailWord_1770486
  simp only [CollatzResearch.WordTrace]
  refine ⟨4035933091489941986288207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43049952975892714520407541 4035933091489941986288207)
  ·
    refine ⟨6053899637234912979432311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4035933091489941986288207 6053899637234912979432311)
    ·
      refine ⟨9080849455852369469148467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6053899637234912979432311 9080849455852369469148467)
      ·
        refine ⟨13621274183778554203722701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9080849455852369469148467 13621274183778554203722701)
        ·
          refine ⟨5107977818916957826396013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13621274183778554203722701 5107977818916957826396013)
          ·
            refine ⟨1915491682093859184898505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5107977818916957826396013 1915491682093859184898505)
            ·
              refine ⟨1436618761570394388673879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1915491682093859184898505 1436618761570394388673879)
              ·
                refine ⟨2154928142355591583010819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1436618761570394388673879 2154928142355591583010819)
                ·
                  refine ⟨3232392213533387374516229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2154928142355591583010819 3232392213533387374516229)
                  ·
                    refine ⟨606073540037510132721793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3232392213533387374516229 606073540037510132721793)
                    ·
                      rfl

theorem cell22_1770486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_1770486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1770486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1770486 prefixEnd_1770486 := by exact prefixLift 1770486
  have htrace : WordTrace (prefixWord ++ tailWord_1770486) baseStart_1770486 baseEnd_1770486 := by
    simpa [prefixWord, tailWord_1770486, baseEnd_1770486] using wordTrace_append hprefix tailTrace_1770486
  have hstable : (prefixWord ++ tailWord_1770486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770486).length < 2 ^ (prefixWord ++ tailWord_1770486).sum := by decide
  have hdescent : baseEnd_1770486 < baseStart_1770486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770527 : List Nat := [1, 1, 2, 4, 1, 3, 2, 2, 3, 3]
def baseStart_1770527 : Nat := 118140960795 + 1770527 * 2 ^ 59
def prefixEnd_1770527 : Nat := 4983230072969 + 3 ^ 40 * 1770527 * 2
def baseEnd_1770527 : Nat := 606087575175399692446667

theorem tailTrace_1770527 : CollatzResearch.WordTrace tailWord_1770527 prefixEnd_1770527 606087575175399692446667 := by
  unfold tailWord_1770527
  simp only [CollatzResearch.WordTrace]
  refine ⟨64576424856690535782853835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43050949904460357188569223 64576424856690535782853835)
  ·
    refine ⟨96864637285035803674280753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64576424856690535782853835 96864637285035803674280753)
    ·
      refine ⟨72648477963776852755710565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96864637285035803674280753 72648477963776852755710565)
      ·
        refine ⟨13621589618208159891695731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72648477963776852755710565 13621589618208159891695731)
        ·
          refine ⟨20432384427312239837543597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13621589618208159891695731 20432384427312239837543597)
          ·
            refine ⟨7662144160242089939078849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20432384427312239837543597 7662144160242089939078849)
            ·
              refine ⟨5746608120181567454309137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7662144160242089939078849 5746608120181567454309137)
              ·
                refine ⟨4309956090136175590731853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5746608120181567454309137 4309956090136175590731853)
                ·
                  refine ⟨1616233533801065846524445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4309956090136175590731853 1616233533801065846524445)
                  ·
                    refine ⟨606087575175399692446667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1616233533801065846524445 606087575175399692446667)
                    ·
                      rfl

theorem cell22_1770527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2, 3, 3].length) (baseStart_1770527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1770527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1770527 prefixEnd_1770527 := by exact prefixLift 1770527
  have htrace : WordTrace (prefixWord ++ tailWord_1770527) baseStart_1770527 baseEnd_1770527 := by
    simpa [prefixWord, tailWord_1770527, baseEnd_1770527] using wordTrace_append hprefix tailTrace_1770527
  have hstable : (prefixWord ++ tailWord_1770527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770527).length < 2 ^ (prefixWord ++ tailWord_1770527).sum := by decide
  have hdescent : baseEnd_1770527 < baseStart_1770527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770561 : List Nat := [1, 2, 5, 1, 3, 2, 1, 1, 3, 3]
def baseStart_1770561 : Nat := 118140960795 + 1770561 * 2 ^ 59
def prefixEnd_1770561 : Nat := 4983230072969 + 3 ^ 40 * 1770561 * 2
def baseEnd_1770561 : Nat := 606099214070234937096563

theorem tailTrace_1770561 : CollatzResearch.WordTrace tailWord_1770561 prefixEnd_1770561 606099214070234937096563 := by
  unfold tailWord_1770561
  simp only [CollatzResearch.WordTrace]
  refine ⟨64577664938567359589591537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43051776625711573059727691 64577664938567359589591537)
  ·
    refine ⟨48433248703925519692193653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64577664938567359589591537 48433248703925519692193653)
    ·
      refine ⟨4540617065993017471143155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48433248703925519692193653 4540617065993017471143155)
      ·
        refine ⟨6810925598989526206714733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4540617065993017471143155 6810925598989526206714733)
        ·
          refine ⟨2554097099621072327518025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6810925598989526206714733 2554097099621072327518025)
          ·
            refine ⟨1915572824715804245638519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2554097099621072327518025 1915572824715804245638519)
            ·
              refine ⟨2873359237073706368457779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1915572824715804245638519 2873359237073706368457779)
              ·
                refine ⟨4310038855610559552686669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2873359237073706368457779 4310038855610559552686669)
                ·
                  refine ⟨1616264570853959832257501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4310038855610559552686669 1616264570853959832257501)
                  ·
                    refine ⟨606099214070234937096563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1616264570853959832257501 606099214070234937096563)
                    ·
                      rfl

theorem cell22_1770561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_1770561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1770561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1770561 prefixEnd_1770561 := by exact prefixLift 1770561
  have htrace : WordTrace (prefixWord ++ tailWord_1770561) baseStart_1770561 baseEnd_1770561 := by
    simpa [prefixWord, tailWord_1770561, baseEnd_1770561] using wordTrace_append hprefix tailTrace_1770561
  have hstable : (prefixWord ++ tailWord_1770561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770561).length < 2 ^ (prefixWord ++ tailWord_1770561).sum := by decide
  have hdescent : baseEnd_1770561 < baseStart_1770561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770604 : List Nat := [2, 2, 1, 1, 3, 2, 5, 1, 1, 4]
def baseStart_1770604 : Nat := 118140960795 + 1770604 * 2 ^ 59
def prefixEnd_1770604 : Nat := 4983230072969 + 3 ^ 40 * 1770604 * 2
def baseEnd_1770604 : Nat := 606113933848997158271431

theorem tailTrace_1770604 : CollatzResearch.WordTrace tailWord_1770604 prefixEnd_1770604 606113933848997158271431 := by
  unfold tailWord_1770604
  simp only [CollatzResearch.WordTrace]
  refine ⟨32289616638705788966703433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43052822184941051955604577 32289616638705788966703433)
  ·
    refine ⟨24217212479029341725027575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32289616638705788966703433 24217212479029341725027575)
    ·
      refine ⟨36325818718544012587541363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24217212479029341725027575 36325818718544012587541363)
      ·
        refine ⟨54488728077816018881312045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36325818718544012587541363 54488728077816018881312045)
        ·
          refine ⟨20433273029181007080492017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54488728077816018881312045 20433273029181007080492017)
          ·
            refine ⟨15324954771885755310369013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20433273029181007080492017 15324954771885755310369013)
            ·
              refine ⟨1436714509864289560347095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15324954771885755310369013 1436714509864289560347095)
              ·
                refine ⟨2155071764796434340520643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1436714509864289560347095 2155071764796434340520643)
                ·
                  refine ⟨3232607647194651510780965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2155071764796434340520643 3232607647194651510780965)
                  ·
                    refine ⟨606113933848997158271431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3232607647194651510780965 606113933848997158271431)
                    ·
                      rfl

theorem cell22_1770604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 4].length) (baseStart_1770604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1770604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1770604 prefixEnd_1770604 := by exact prefixLift 1770604
  have htrace : WordTrace (prefixWord ++ tailWord_1770604) baseStart_1770604 baseEnd_1770604 := by
    simpa [prefixWord, tailWord_1770604, baseEnd_1770604] using wordTrace_append hprefix tailTrace_1770604
  have hstable : (prefixWord ++ tailWord_1770604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770604).length < 2 ^ (prefixWord ++ tailWord_1770604).sum := by decide
  have hdescent : baseEnd_1770604 < baseStart_1770604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770634 : List Nat := [3, 1, 2, 3, 1, 1, 1, 5, 2, 3]
def baseStart_1770634 : Nat := 118140960795 + 1770634 * 2 ^ 59
def prefixEnd_1770634 : Nat := 4983230072969 + 3 ^ 40 * 1770634 * 2
def baseEnd_1770634 : Nat := 606124203462087080021339

theorem tailTrace_1770634 : CollatzResearch.WordTrace tailWord_1770634 prefixEnd_1770634 606124203462087080021339 := by
  unfold tailWord_1770634
  simp only [CollatzResearch.WordTrace]
  refine ⟨16145081866825723264249739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43053551644868595371332637 16145081866825723264249739)
  ·
    refine ⟨24217622800238584896374609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16145081866825723264249739 24217622800238584896374609)
    ·
      refine ⟨18163217100178938672280957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24217622800238584896374609 18163217100178938672280957)
      ·
        refine ⟨6811206412567102002105359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18163217100178938672280957 6811206412567102002105359)
        ·
          refine ⟨10216809618850653003158039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6811206412567102002105359 10216809618850653003158039)
          ·
            refine ⟨15325214428275979504737059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10216809618850653003158039 15325214428275979504737059)
            ·
              refine ⟨22987821642413969257105589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15325214428275979504737059 22987821642413969257105589)
              ·
                refine ⟨2155108278976309617853649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22987821642413969257105589 2155108278976309617853649)
                ·
                  refine ⟨1616331209232232213390237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2155108278976309617853649 1616331209232232213390237)
                  ·
                    refine ⟨606124203462087080021339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1616331209232232213390237 606124203462087080021339)
                    ·
                      rfl

theorem cell22_1770634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 5, 2, 3].length) (baseStart_1770634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1770634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1770634 prefixEnd_1770634 := by exact prefixLift 1770634
  have htrace : WordTrace (prefixWord ++ tailWord_1770634) baseStart_1770634 baseEnd_1770634 := by
    simpa [prefixWord, tailWord_1770634, baseEnd_1770634] using wordTrace_append hprefix tailTrace_1770634
  have hstable : (prefixWord ++ tailWord_1770634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770634).length < 2 ^ (prefixWord ++ tailWord_1770634).sum := by decide
  have hdescent : baseEnd_1770634 < baseStart_1770634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770645 : List Nat := [1, 3, 2, 1, 1, 1, 2, 1, 1, 9]
def baseStart_1770645 : Nat := 118140960795 + 1770645 * 2 ^ 59
def prefixEnd_1770645 : Nat := 4983230072969 + 3 ^ 40 * 1770645 * 2
def baseEnd_1770645 : Nat := 606127968986886717996305

theorem tailTrace_1770645 : CollatzResearch.WordTrace tailWord_1770645 prefixEnd_1770645 606127968986886717996305 := by
  unfold tailWord_1770645
  simp only [CollatzResearch.WordTrace]
  refine ⟨64580728670263041935649389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43053819113508694623766259 64580728670263041935649389)
  ·
    refine ⟨24217773251348640725868521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64580728670263041935649389 24217773251348640725868521)
    ·
      refine ⟨18163329938511480544401391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24217773251348640725868521 18163329938511480544401391)
      ·
        refine ⟨27244994907767220816602087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18163329938511480544401391 27244994907767220816602087)
        ·
          refine ⟨40867492361650831224903131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27244994907767220816602087 40867492361650831224903131)
          ·
            refine ⟨61301238542476246837354697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40867492361650831224903131 61301238542476246837354697)
            ·
              refine ⟨45975928906857185128016023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61301238542476246837354697 45975928906857185128016023)
              ·
                refine ⟨68963893360285777692024035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45975928906857185128016023 68963893360285777692024035)
                ·
                  refine ⟨103445840040428666538036053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68963893360285777692024035 103445840040428666538036053)
                  ·
                    refine ⟨606127968986886717996305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 103445840040428666538036053 606127968986886717996305)
                    ·
                      rfl

theorem cell22_1770645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_1770645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1770645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1770645 prefixEnd_1770645 := by exact prefixLift 1770645
  have htrace : WordTrace (prefixWord ++ tailWord_1770645) baseStart_1770645 baseEnd_1770645 := by
    simpa [prefixWord, tailWord_1770645, baseEnd_1770645] using wordTrace_append hprefix tailTrace_1770645
  have hstable : (prefixWord ++ tailWord_1770645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770645).length < 2 ^ (prefixWord ++ tailWord_1770645).sum := by decide
  have hdescent : baseEnd_1770645 < baseStart_1770645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770679 : List Nat := [1, 1, 3, 1, 4, 1, 4, 1, 3, 3]
def baseStart_1770679 : Nat := 118140960795 + 1770679 * 2 ^ 59
def prefixEnd_1770679 : Nat := 4983230072969 + 3 ^ 40 * 1770679 * 2
def baseEnd_1770679 : Nat := 606139607881721962646201

theorem tailTrace_1770679 : CollatzResearch.WordTrace tailWord_1770679 prefixEnd_1770679 606139607881721962646201 := by
  unfold tailWord_1770679
  simp only [CollatzResearch.WordTrace]
  refine ⟨64581968752139865742387091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43054645834759910494924727 64581968752139865742387091)
  ·
    refine ⟨96872953128209798613580637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64581968752139865742387091 96872953128209798613580637)
    ·
      refine ⟨36327357423078674480092739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96872953128209798613580637 36327357423078674480092739)
      ·
        refine ⟨54491036134618011720139109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36327357423078674480092739 54491036134618011720139109)
        ·
          refine ⟨10217069275240877197526083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54491036134618011720139109 10217069275240877197526083)
          ·
            refine ⟨15325603912861315796289125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10217069275240877197526083 15325603912861315796289125)
            ·
              refine ⟨2873550733661496711804211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15325603912861315796289125 2873550733661496711804211)
              ·
                refine ⟨4310326100492245067706317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2873550733661496711804211 4310326100492245067706317)
                ·
                  refine ⟨1616372287684591900389869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4310326100492245067706317 1616372287684591900389869)
                  ·
                    refine ⟨606139607881721962646201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1616372287684591900389869 606139607881721962646201)
                    ·
                      rfl

theorem cell22_1770679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 3, 3].length) (baseStart_1770679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1770679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1770679 prefixEnd_1770679 := by exact prefixLift 1770679
  have htrace : WordTrace (prefixWord ++ tailWord_1770679) baseStart_1770679 baseEnd_1770679 := by
    simpa [prefixWord, tailWord_1770679, baseEnd_1770679] using wordTrace_append hprefix tailTrace_1770679
  have hstable : (prefixWord ++ tailWord_1770679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770679).length < 2 ^ (prefixWord ++ tailWord_1770679).sum := by decide
  have hdescent : baseEnd_1770679 < baseStart_1770679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770752 : List Nat := [2, 1, 1, 2, 1, 1, 3, 5, 1, 5]
def baseStart_1770752 : Nat := 118140960795 + 1770752 * 2 ^ 59
def prefixEnd_1770752 : Nat := 4983230072969 + 3 ^ 40 * 1770752 * 2
def baseEnd_1770752 : Nat := 606164597273574105570977

theorem tailTrace_1770752 : CollatzResearch.WordTrace tailWord_1770752 prefixEnd_1770752 606164597273574105570977 := by
  unfold tailWord_1770752
  simp only [CollatzResearch.WordTrace]
  refine ⟨32292315640437699604897255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43056420853916932806529673 32292315640437699604897255)
  ·
    refine ⟨48438473460656549407345883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32292315640437699604897255 48438473460656549407345883)
    ·
      refine ⟨72657710190984824111018825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48438473460656549407345883 72657710190984824111018825)
      ·
        refine ⟨54493282643238618083264119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72657710190984824111018825 54493282643238618083264119)
        ·
          refine ⟨81739923964857927124896179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54493282643238618083264119 81739923964857927124896179)
          ·
            refine ⟨122609885947286890687344269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81739923964857927124896179 122609885947286890687344269)
            ·
              refine ⟨45978707230232584007754101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122609885947286890687344269 45978707230232584007754101)
              ·
                refine ⟨4310503802834304750726947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45978707230232584007754101 4310503802834304750726947)
                ·
                  refine ⟨6465755704251457126090421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4310503802834304750726947 6465755704251457126090421)
                  ·
                    refine ⟨606164597273574105570977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6465755704251457126090421 606164597273574105570977)
                    ·
                      rfl

theorem cell22_1770752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5, 1, 5].length) (baseStart_1770752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1770752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1770752 prefixEnd_1770752 := by exact prefixLift 1770752
  have htrace : WordTrace (prefixWord ++ tailWord_1770752) baseStart_1770752 baseEnd_1770752 := by
    simpa [prefixWord, tailWord_1770752, baseEnd_1770752] using wordTrace_append hprefix tailTrace_1770752
  have hstable : (prefixWord ++ tailWord_1770752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770752).length < 2 ^ (prefixWord ++ tailWord_1770752).sum := by decide
  have hdescent : baseEnd_1770752 < baseStart_1770752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770756 : List Nat := [2, 3, 2, 2, 2, 1, 3, 2, 1, 4]
def baseStart_1770756 : Nat := 118140960795 + 1770756 * 2 ^ 59
def prefixEnd_1770756 : Nat := 4983230072969 + 3 ^ 40 * 1770756 * 2
def baseEnd_1770756 : Nat := 606165966555319428470965

theorem tailTrace_1770756 : CollatzResearch.WordTrace tailWord_1770756 prefixEnd_1770756 606165966555319428470965 := by
  unfold tailWord_1770756
  simp only [CollatzResearch.WordTrace]
  refine ⟨32292388586430453946470061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43056518115240605261960081 32292388586430453946470061)
  ·
    refine ⟨12109645719911420229926273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32292388586430453946470061 12109645719911420229926273)
    ·
      refine ⟨9082234289933565172444705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12109645719911420229926273 9082234289933565172444705)
      ·
        refine ⟨6811675717450173879333529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9082234289933565172444705 6811675717450173879333529)
        ·
          refine ⟨5108756788087630409500147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6811675717450173879333529 5108756788087630409500147)
          ·
            refine ⟨7663135182131445614250221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5108756788087630409500147 7663135182131445614250221)
            ·
              refine ⟨2873675693299292105343833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7663135182131445614250221 2873675693299292105343833)
              ·
                refine ⟨2155256769974469079007875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2873675693299292105343833 2155256769974469079007875)
                ·
                  refine ⟨3232885154961703618511813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2155256769974469079007875 3232885154961703618511813)
                  ·
                    refine ⟨606165966555319428470965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3232885154961703618511813 606165966555319428470965)
                    ·
                      rfl

theorem cell22_1770756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_1770756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1770756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1770756 prefixEnd_1770756 := by exact prefixLift 1770756
  have htrace : WordTrace (prefixWord ++ tailWord_1770756) baseStart_1770756 baseEnd_1770756 := by
    simpa [prefixWord, tailWord_1770756, baseEnd_1770756] using wordTrace_append hprefix tailTrace_1770756
  have hstable : (prefixWord ++ tailWord_1770756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770756).length < 2 ^ (prefixWord ++ tailWord_1770756).sum := by decide
  have hdescent : baseEnd_1770756 < baseStart_1770756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770822 : List Nat := [6, 1, 1, 3, 1, 1, 2, 3, 4]
def baseStart_1770822 : Nat := 118140960795 + 1770822 * 2 ^ 59
def prefixEnd_1770822 : Nat := 4983230072969 + 3 ^ 40 * 1770822 * 2
def baseEnd_1770822 : Nat := 202062853234705752106921

theorem tailTrace_1770822 : CollatzResearch.WordTrace tailWord_1770822 prefixEnd_1770822 202062853234705752106921 := by
  unfold tailWord_1770822
  simp only [CollatzResearch.WordTrace]
  refine ⟨2018349512206931286401335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 43058122927081200776561813 2018349512206931286401335)
  ·
    refine ⟨3027524268310396929602003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2018349512206931286401335 3027524268310396929602003)
    ·
      refine ⟨4541286402465595394403005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3027524268310396929602003 4541286402465595394403005)
      ·
        refine ⟨1702982400924598272901127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4541286402465595394403005 1702982400924598272901127)
        ·
          refine ⟨2554473601386897409351691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1702982400924598272901127 2554473601386897409351691)
          ·
            refine ⟨3831710402080346114027537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2554473601386897409351691 3831710402080346114027537)
            ·
              refine ⟨2873782801560259585520653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3831710402080346114027537 2873782801560259585520653)
              ·
                refine ⟨1077668550585097344570245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2873782801560259585520653 1077668550585097344570245)
                ·
                  refine ⟨202062853234705752106921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1077668550585097344570245 202062853234705752106921)
                  ·
                    rfl

theorem cell22_1770822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_1770822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1770822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1770822 prefixEnd_1770822 := by exact prefixLift 1770822
  have htrace : WordTrace (prefixWord ++ tailWord_1770822) baseStart_1770822 baseEnd_1770822 := by
    simpa [prefixWord, tailWord_1770822, baseEnd_1770822] using wordTrace_append hprefix tailTrace_1770822
  have hstable : (prefixWord ++ tailWord_1770822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770822).length < 2 ^ (prefixWord ++ tailWord_1770822).sum := by decide
  have hdescent : baseEnd_1770822 < baseStart_1770822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770848 : List Nat := [2, 1, 1, 3, 4, 1, 2, 4, 1, 3]
def baseStart_1770848 : Nat := 118140960795 + 1770848 * 2 ^ 59
def prefixEnd_1770848 : Nat := 4983230072969 + 3 ^ 40 * 1770848 * 2
def baseEnd_1770848 : Nat := 606197460035461855170683

theorem tailTrace_1770848 : CollatzResearch.WordTrace tailWord_1770848 prefixEnd_1770848 606197460035461855170683 := by
  unfold tailWord_1770848
  simp only [CollatzResearch.WordTrace]
  refine ⟨32294066344263803802644599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43058755125685071736859465 32294066344263803802644599)
  ·
    refine ⟨48441099516395705703966899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32294066344263803802644599 48441099516395705703966899)
    ·
      refine ⟨72661649274593558555950349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48441099516395705703966899 72661649274593558555950349)
      ·
        refine ⟨27248118477972584458481381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72661649274593558555950349 27248118477972584458481381)
        ·
          refine ⟨5109022214619859585965259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27248118477972584458481381 5109022214619859585965259)
          ·
            refine ⟨7663533321929789378947889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5109022214619859585965259 7663533321929789378947889)
            ·
              refine ⟨5747649991447342034210917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7663533321929789378947889 5747649991447342034210917)
              ·
                refine ⟨1077684373396376631414547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5747649991447342034210917 1077684373396376631414547)
                ·
                  refine ⟨1616526560094564947121821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1077684373396376631414547 1616526560094564947121821)
                  ·
                    refine ⟨606197460035461855170683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1616526560094564947121821 606197460035461855170683)
                    ·
                      rfl

theorem cell22_1770848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 4, 1, 3].length) (baseStart_1770848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1770848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1770848 prefixEnd_1770848 := by exact prefixLift 1770848
  have htrace : WordTrace (prefixWord ++ tailWord_1770848) baseStart_1770848 baseEnd_1770848 := by
    simpa [prefixWord, tailWord_1770848, baseEnd_1770848] using wordTrace_append hprefix tailTrace_1770848
  have hstable : (prefixWord ++ tailWord_1770848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770848).length < 2 ^ (prefixWord ++ tailWord_1770848).sum := by decide
  have hdescent : baseEnd_1770848 < baseStart_1770848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770857 : List Nat := [1, 2, 1, 1, 1, 3, 2, 1, 2, 8]
def baseStart_1770857 : Nat := 118140960795 + 1770857 * 2 ^ 59
def prefixEnd_1770857 : Nat := 4983230072969 + 3 ^ 40 * 1770857 * 2
def baseEnd_1770857 : Nat := 606200540919388831695655

theorem tailTrace_1770857 : CollatzResearch.WordTrace tailWord_1770857 prefixEnd_1770857 606200540919388831695655 := by
  unfold tailWord_1770857
  simp only [CollatzResearch.WordTrace]
  refine ⟨64588460945495002142366825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43058973963663334761577883 64588460945495002142366825)
  ·
    refine ⟨48441345709121251606775119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64588460945495002142366825 48441345709121251606775119)
    ·
      refine ⟨72662018563681877410162679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48441345709121251606775119 72662018563681877410162679)
      ·
        refine ⟨108993027845522816115244019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72662018563681877410162679 108993027845522816115244019)
        ·
          refine ⟨163489541768284224172866029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108993027845522816115244019 163489541768284224172866029)
          ·
            refine ⟨61308578163106584064824761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163489541768284224172866029 61308578163106584064824761)
            ·
              refine ⟨45981433622329938048618571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61308578163106584064824761 45981433622329938048618571)
              ·
                refine ⟨68972150433494907072927857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45981433622329938048618571 68972150433494907072927857)
                ·
                  refine ⟨51729112825121180304695893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68972150433494907072927857 51729112825121180304695893)
                  ·
                    refine ⟨606200540919388831695655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 51729112825121180304695893 606200540919388831695655)
                    ·
                      rfl

theorem cell22_1770857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 8].length) (baseStart_1770857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1770857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1770857 prefixEnd_1770857 := by exact prefixLift 1770857
  have htrace : WordTrace (prefixWord ++ tailWord_1770857) baseStart_1770857 baseEnd_1770857 := by
    simpa [prefixWord, tailWord_1770857, baseEnd_1770857] using wordTrace_append hprefix tailTrace_1770857
  have hstable : (prefixWord ++ tailWord_1770857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770857).length < 2 ^ (prefixWord ++ tailWord_1770857).sum := by decide
  have hdescent : baseEnd_1770857 < baseStart_1770857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770882 : List Nat := [3, 4, 2, 1, 1, 1, 3, 3, 1, 3]
def baseStart_1770882 : Nat := 118140960795 + 1770882 * 2 ^ 59
def prefixEnd_1770882 : Nat := 4983230072969 + 3 ^ 40 * 1770882 * 2
def baseEnd_1770882 : Nat := 606209098930297099820579

theorem tailTrace_1770882 : CollatzResearch.WordTrace tailWord_1770882 prefixEnd_1770882 606209098930297099820579 := by
  unfold tailWord_1770882
  simp only [CollatzResearch.WordTrace]
  refine ⟨16147343192601107853006725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43059581846936287608017933 16147343192601107853006725)
  ·
    refine ⟨3027626848612707722438761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16147343192601107853006725 3027626848612707722438761)
    ·
      refine ⟨2270720136459530791829071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3027626848612707722438761 2270720136459530791829071)
      ·
        refine ⟨3406080204689296187743607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2270720136459530791829071 3406080204689296187743607)
        ·
          refine ⟨5109120307033944281615411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3406080204689296187743607 5109120307033944281615411)
          ·
            refine ⟨7663680460550916422423117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5109120307033944281615411 7663680460550916422423117)
            ·
              refine ⟨2873880172706593658408669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7663680460550916422423117 2873880172706593658408669)
              ·
                refine ⟨1077705064764972621903251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2873880172706593658408669 1077705064764972621903251)
                ·
                  refine ⟨1616557597147458932854877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1077705064764972621903251 1616557597147458932854877)
                  ·
                    refine ⟨606209098930297099820579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1616557597147458932854877 606209098930297099820579)
                    ·
                      rfl

theorem cell22_1770882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_1770882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1770882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1770882 prefixEnd_1770882 := by exact prefixLift 1770882
  have htrace : WordTrace (prefixWord ++ tailWord_1770882) baseStart_1770882 baseEnd_1770882 := by
    simpa [prefixWord, tailWord_1770882, baseEnd_1770882] using wordTrace_append hprefix tailTrace_1770882
  have hstable : (prefixWord ++ tailWord_1770882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770882).length < 2 ^ (prefixWord ++ tailWord_1770882).sum := by decide
  have hdescent : baseEnd_1770882 < baseStart_1770882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770925 : List Nat := [1, 5, 2, 2, 1, 3, 1, 2, 1, 4]
def baseStart_1770925 : Nat := 118140960795 + 1770925 * 2 ^ 59
def prefixEnd_1770925 : Nat := 4983230072969 + 3 ^ 40 * 1770925 * 2
def baseEnd_1770925 : Nat := 606223818709059320995447

theorem tailTrace_1770925 : CollatzResearch.WordTrace tailWord_1770925 prefixEnd_1770925 606223818709059320995447 := by
  unfold tailWord_1770925
  simp only [CollatzResearch.WordTrace]
  refine ⟨64590941109248649755842229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43060627406165766503894819 64590941109248649755842229)
  ·
    refine ⟨6055400728992060914610209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64590941109248649755842229 6055400728992060914610209)
    ·
      refine ⟨4541550546744045685957657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6055400728992060914610209 4541550546744045685957657)
      ·
        refine ⟨3406162910058034264468243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4541550546744045685957657 3406162910058034264468243)
        ·
          refine ⟨5109244365087051396702365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3406162910058034264468243 5109244365087051396702365)
          ·
            refine ⟨1915966636907644273763387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5109244365087051396702365 1915966636907644273763387)
            ·
              refine ⟨2873949955361466410645081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1915966636907644273763387 2873949955361466410645081)
              ·
                refine ⟨2155462466521099807983811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2873949955361466410645081 2155462466521099807983811)
                ·
                  refine ⟨3233193699781649711975717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2155462466521099807983811 3233193699781649711975717)
                  ·
                    refine ⟨606223818709059320995447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3233193699781649711975717 606223818709059320995447)
                    ·
                      rfl

theorem cell22_1770925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_1770925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1770925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1770925 prefixEnd_1770925 := by exact prefixLift 1770925
  have htrace : WordTrace (prefixWord ++ tailWord_1770925) baseStart_1770925 baseEnd_1770925 := by
    simpa [prefixWord, tailWord_1770925, baseEnd_1770925] using wordTrace_append hprefix tailTrace_1770925
  have hstable : (prefixWord ++ tailWord_1770925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770925).length < 2 ^ (prefixWord ++ tailWord_1770925).sum := by decide
  have hdescent : baseEnd_1770925 < baseStart_1770925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770983 : List Nat := [1, 1, 5, 2, 1, 3, 1, 2, 3, 3]
def baseStart_1770983 : Nat := 118140960795 + 1770983 * 2 ^ 59
def prefixEnd_1770983 : Nat := 4983230072969 + 3 ^ 40 * 1770983 * 2
def baseEnd_1770983 : Nat := 606243673294366503045269

theorem tailTrace_1770983 : CollatzResearch.WordTrace tailWord_1770983 prefixEnd_1770983 606243673294366503045269 := by
  unfold tailWord_1770983
  simp only [CollatzResearch.WordTrace]
  refine ⟨64593056543038525661453603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43062037695359017107635735 64593056543038525661453603)
  ·
    refine ⟨96889584814557788492180405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64593056543038525661453603 96889584814557788492180405)
    ·
      refine ⟨9083398576364792671141913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 96889584814557788492180405 9083398576364792671141913)
      ·
        refine ⟨6812548932273594503356435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9083398576364792671141913 6812548932273594503356435)
        ·
          refine ⟨10218823398410391755034653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6812548932273594503356435 10218823398410391755034653)
          ·
            refine ⟨3832058774403896908137995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10218823398410391755034653 3832058774403896908137995)
            ·
              refine ⟨5748088161605845362206993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3832058774403896908137995 5748088161605845362206993)
              ·
                refine ⟨4311066121204384021655245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5748088161605845362206993 4311066121204384021655245)
                ·
                  refine ⟨1616649795451644008120717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4311066121204384021655245 1616649795451644008120717)
                  ·
                    refine ⟨606243673294366503045269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1616649795451644008120717 606243673294366503045269)
                    ·
                      rfl

theorem cell22_1770983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_1770983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1770983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1770983 prefixEnd_1770983 := by exact prefixLift 1770983
  have htrace : WordTrace (prefixWord ++ tailWord_1770983) baseStart_1770983 baseEnd_1770983 := by
    simpa [prefixWord, tailWord_1770983, baseEnd_1770983] using wordTrace_append hprefix tailTrace_1770983
  have hstable : (prefixWord ++ tailWord_1770983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770983).length < 2 ^ (prefixWord ++ tailWord_1770983).sum := by decide
  have hdescent : baseEnd_1770983 < baseStart_1770983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771000 : List Nat := [2, 1, 2, 1, 1, 6, 2, 3, 1, 3]
def baseStart_1771000 : Nat := 118140960795 + 1771000 * 2 ^ 59
def prefixEnd_1771000 : Nat := 4983230072969 + 3 ^ 40 * 1771000 * 2
def baseEnd_1771000 : Nat := 606249492741784125370217

theorem tailTrace_1771000 : CollatzResearch.WordTrace tailWord_1771000 prefixEnd_1771000 606249492741784125370217 := by
  unfold tailWord_1771000
  simp only [CollatzResearch.WordTrace]
  refine ⟨32296838291988468782411227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43062451055984625043214969 32296838291988468782411227)
  ·
    refine ⟨48445257437982703173616841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32296838291988468782411227 48445257437982703173616841)
    ·
      refine ⟨36333943078487027380212631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48445257437982703173616841 36333943078487027380212631)
      ·
        refine ⟨54500914617730541070318947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36333943078487027380212631 54500914617730541070318947)
        ·
          refine ⟨81751371926595811605478421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54500914617730541070318947 81751371926595811605478421)
          ·
            refine ⟨3832095559059178669006801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 81751371926595811605478421 3832095559059178669006801)
            ·
              refine ⟨2874071669294384001755101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3832095559059178669006801 2874071669294384001755101)
              ·
                refine ⟨1077776875985394000658163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2874071669294384001755101 1077776875985394000658163)
                ·
                  refine ⟨1616665313978091000987245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1077776875985394000658163 1616665313978091000987245)
                  ·
                    refine ⟨606249492741784125370217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1616665313978091000987245 606249492741784125370217)
                    ·
                      rfl

theorem cell22_1771000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 3, 1, 3].length) (baseStart_1771000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1771000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1771000 prefixEnd_1771000 := by exact prefixLift 1771000
  have htrace : WordTrace (prefixWord ++ tailWord_1771000) baseStart_1771000 baseEnd_1771000 := by
    simpa [prefixWord, tailWord_1771000, baseEnd_1771000] using wordTrace_append hprefix tailTrace_1771000
  have hstable : (prefixWord ++ tailWord_1771000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771000).length < 2 ^ (prefixWord ++ tailWord_1771000).sum := by decide
  have hdescent : baseEnd_1771000 < baseStart_1771000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771041 : List Nat := [1, 2, 3, 2, 2, 2, 2, 2, 6]
def baseStart_1771041 : Nat := 118140960795 + 1771041 * 2 ^ 59
def prefixEnd_1771041 : Nat := 4983230072969 + 3 ^ 40 * 1771041 * 2
def baseEnd_1771041 : Nat := 202087842626557895031697

theorem tailTrace_1771041 : CollatzResearch.WordTrace tailWord_1771041 prefixEnd_1771041 202087842626557895031697 := by
  unfold tailWord_1771041
  simp only [CollatzResearch.WordTrace]
  refine ⟨64595171976828401567064977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43063447984552267711376651 64595171976828401567064977)
  ·
    refine ⟨48446378982621301175298733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64595171976828401567064977 48446378982621301175298733)
    ·
      refine ⟨18167392118482987940737025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48446378982621301175298733 18167392118482987940737025)
      ·
        refine ⟨13625544088862240955552769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18167392118482987940737025 13625544088862240955552769)
        ·
          refine ⟨10219158066646680716664577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13625544088862240955552769 10219158066646680716664577)
          ·
            refine ⟨7664368549985010537498433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10219158066646680716664577 7664368549985010537498433)
            ·
              refine ⟨5748276412488757903123825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7664368549985010537498433 5748276412488757903123825)
              ·
                refine ⟨4311207309366568427342869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5748276412488757903123825 4311207309366568427342869)
                ·
                  refine ⟨202087842626557895031697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4311207309366568427342869 202087842626557895031697)
                  ·
                    rfl

theorem cell22_1771041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2, 6].length) (baseStart_1771041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1771041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1771041 prefixEnd_1771041 := by exact prefixLift 1771041
  have htrace : WordTrace (prefixWord ++ tailWord_1771041) baseStart_1771041 baseEnd_1771041 := by
    simpa [prefixWord, tailWord_1771041, baseEnd_1771041] using wordTrace_append hprefix tailTrace_1771041
  have hstable : (prefixWord ++ tailWord_1771041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771041).length < 2 ^ (prefixWord ++ tailWord_1771041).sum := by decide
  have hdescent : baseEnd_1771041 < baseStart_1771041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771071 : List Nat := [1, 1, 2, 2, 3, 3, 1, 1, 4, 4]
def baseStart_1771071 : Nat := 118140960795 + 1771071 * 2 ^ 59
def prefixEnd_1771071 : Nat := 4983230072969 + 3 ^ 40 * 1771071 * 2
def baseEnd_1771071 : Nat := 606273797492763606844999

theorem tailTrace_1771071 : CollatzResearch.WordTrace tailWord_1771071 prefixEnd_1771071 606273797492763606844999 := by
  unfold tailWord_1771071
  simp only [CollatzResearch.WordTrace]
  refine ⟨64596266166719716690657067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43064177444479811127104711 64596266166719716690657067)
  ·
    refine ⟨96894399250079575035985601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64596266166719716690657067 96894399250079575035985601)
    ·
      refine ⟨72670799437559681276989201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96894399250079575035985601 72670799437559681276989201)
      ·
        refine ⟨54503099578169760957741901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72670799437559681276989201 54503099578169760957741901)
        ·
          refine ⟨20438662341813660359153213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54503099578169760957741901 20438662341813660359153213)
          ·
            refine ⟨7664498378180122634682455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20438662341813660359153213 7664498378180122634682455)
            ·
              refine ⟨11496747567270183952023683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7664498378180122634682455 11496747567270183952023683)
              ·
                refine ⟨17245121350905275928035525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11496747567270183952023683 17245121350905275928035525)
                ·
                  refine ⟨3233460253294739236506661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17245121350905275928035525 3233460253294739236506661)
                  ·
                    refine ⟨606273797492763606844999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3233460253294739236506661 606273797492763606844999)
                    ·
                      rfl

theorem cell22_1771071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 4, 4].length) (baseStart_1771071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1771071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1771071 prefixEnd_1771071 := by exact prefixLift 1771071
  have htrace : WordTrace (prefixWord ++ tailWord_1771071) baseStart_1771071 baseEnd_1771071 := by
    simpa [prefixWord, tailWord_1771071, baseEnd_1771071] using wordTrace_append hprefix tailTrace_1771071
  have hstable : (prefixWord ++ tailWord_1771071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771071).length < 2 ^ (prefixWord ++ tailWord_1771071).sum := by decide
  have hdescent : baseEnd_1771071 < baseStart_1771071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771073 : List Nat := [1, 2, 5, 1, 1, 1, 1, 3, 4, 3]
def baseStart_1771073 : Nat := 118140960795 + 1771073 * 2 ^ 59
def prefixEnd_1771073 : Nat := 4983230072969 + 3 ^ 40 * 1771073 * 2
def baseEnd_1771073 : Nat := 606274482133636268294993

theorem tailTrace_1771073 : CollatzResearch.WordTrace tailWord_1771073 prefixEnd_1771073 606274482133636268294993 := by
  unfold tailWord_1771073
  simp only [CollatzResearch.WordTrace]
  refine ⟨64596339112712471032229873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43064226075141647354819915 64596339112712471032229873)
  ·
    refine ⟨48447254334534353274172405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64596339112712471032229873 48447254334534353274172405)
    ·
      refine ⟨4541930093862595619453663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48447254334534353274172405 4541930093862595619453663)
      ·
        refine ⟨6812895140793893429180495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4541930093862595619453663 6812895140793893429180495)
        ·
          refine ⟨10219342711190840143770743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6812895140793893429180495 10219342711190840143770743)
          ·
            refine ⟨15329014066786260215656115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10219342711190840143770743 15329014066786260215656115)
            ·
              refine ⟨22993521100179390323484173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15329014066786260215656115 22993521100179390323484173)
              ·
                refine ⟨8622570412567271371306565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22993521100179390323484173 8622570412567271371306565)
                ·
                  refine ⟨1616731952356363382119981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8622570412567271371306565 1616731952356363382119981)
                  ·
                    refine ⟨606274482133636268294993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1616731952356363382119981 606274482133636268294993)
                    ·
                      rfl

theorem cell22_1771073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_1771073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1771073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1771073 prefixEnd_1771073 := by exact prefixLift 1771073
  have htrace : WordTrace (prefixWord ++ tailWord_1771073) baseStart_1771073 baseEnd_1771073 := by
    simpa [prefixWord, tailWord_1771073, baseEnd_1771073] using wordTrace_append hprefix tailTrace_1771073
  have hstable : (prefixWord ++ tailWord_1771073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771073).length < 2 ^ (prefixWord ++ tailWord_1771073).sum := by decide
  have hdescent : baseEnd_1771073 < baseStart_1771073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771090 : List Nat := [3, 2, 2, 1, 2, 3, 1, 3, 2, 3]
def baseStart_1771090 : Nat := 118140960795 + 1771090 * 2 ^ 59
def prefixEnd_1771090 : Nat := 4983230072969 + 3 ^ 40 * 1771090 * 2
def baseEnd_1771090 : Nat := 606280301581053890619941

theorem tailTrace_1771090 : CollatzResearch.WordTrace tailWord_1771090 prefixEnd_1771090 606280301581053890619941 := by
  unfold tailWord_1771090
  simp only [CollatzResearch.WordTrace]
  refine ⟨16149239788412720733899681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43064639435767255290399149 16149239788412720733899681)
  ·
    refine ⟨12111929841309540550424761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16149239788412720733899681 12111929841309540550424761)
    ·
      refine ⟨9083947380982155412818571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12111929841309540550424761 9083947380982155412818571)
      ·
        refine ⟨13625921071473233119227857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9083947380982155412818571 13625921071473233119227857)
        ·
          refine ⟨10219440803604924839420893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13625921071473233119227857 10219440803604924839420893)
          ·
            refine ⟨3832290301351846814782835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10219440803604924839420893 3832290301351846814782835)
            ·
              refine ⟨5748435452027770222174253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3832290301351846814782835 5748435452027770222174253)
              ·
                refine ⟨2155663294510413833315345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5748435452027770222174253 2155663294510413833315345)
                ·
                  refine ⟨1616747470882810374986509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2155663294510413833315345 1616747470882810374986509)
                  ·
                    refine ⟨606280301581053890619941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1616747470882810374986509 606280301581053890619941)
                    ·
                      rfl

theorem cell22_1771090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_1771090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1771090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1771090 prefixEnd_1771090 := by exact prefixLift 1771090
  have htrace : WordTrace (prefixWord ++ tailWord_1771090) baseStart_1771090 baseEnd_1771090 := by
    simpa [prefixWord, tailWord_1771090, baseEnd_1771090] using wordTrace_append hprefix tailTrace_1771090
  have hstable : (prefixWord ++ tailWord_1771090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771090).length < 2 ^ (prefixWord ++ tailWord_1771090).sum := by decide
  have hdescent : baseEnd_1771090 < baseStart_1771090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771212 : List Nat := [2, 2, 1, 5, 2, 1, 2, 2, 1, 4]
def baseStart_1771212 : Nat := 118140960795 + 1771212 * 2 ^ 59
def prefixEnd_1771212 : Nat := 4983230072969 + 3 ^ 40 * 1771212 * 2
def baseEnd_1771212 : Nat := 606322064674286239069567

theorem tailTrace_1771212 : CollatzResearch.WordTrace tailWord_1771212 prefixEnd_1771212 606322064674286239069567 := by
  unfold tailWord_1771212
  simp only [CollatzResearch.WordTrace]
  refine ⟨32300704429604448885769945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43067605906139265181026593 32300704429604448885769945)
  ·
    refine ⟨24225528322203336664327459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32300704429604448885769945 24225528322203336664327459)
    ·
      refine ⟨36338292483305004996491189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24225528322203336664327459 36338292483305004996491189)
      ·
        refine ⟨3406714920309844218421049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36338292483305004996491189 3406714920309844218421049)
        ·
          refine ⟨2555036190232383163815787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3406714920309844218421049 2555036190232383163815787)
          ·
            refine ⟨3832554285348574745723681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2555036190232383163815787 3832554285348574745723681)
            ·
              refine ⟨2874415714011431059292761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3832554285348574745723681 2874415714011431059292761)
              ·
                refine ⟨2155811785508573294469571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2874415714011431059292761 2155811785508573294469571)
                ·
                  refine ⟨3233717678262859941704357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2155811785508573294469571 3233717678262859941704357)
                  ·
                    refine ⟨606322064674286239069567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3233717678262859941704357 606322064674286239069567)
                    ·
                      rfl

theorem cell22_1771212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 2, 1, 4].length) (baseStart_1771212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1771212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1771212 prefixEnd_1771212 := by exact prefixLift 1771212
  have htrace : WordTrace (prefixWord ++ tailWord_1771212) baseStart_1771212 baseEnd_1771212 := by
    simpa [prefixWord, tailWord_1771212, baseEnd_1771212] using wordTrace_append hprefix tailTrace_1771212
  have hstable : (prefixWord ++ tailWord_1771212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771212).length < 2 ^ (prefixWord ++ tailWord_1771212).sum := by decide
  have hdescent : baseEnd_1771212 < baseStart_1771212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771223 : List Nat := [1, 1, 3, 2, 1, 3, 2, 3, 2, 4]
def baseStart_1771223 : Nat := 118140960795 + 1771223 * 2 ^ 59
def prefixEnd_1771223 : Nat := 4983230072969 + 3 ^ 40 * 1771223 * 2
def baseEnd_1771223 : Nat := 606325830199085877044533

theorem tailTrace_1771223 : CollatzResearch.WordTrace tailWord_1771223 prefixEnd_1771223 606325830199085877044533 := by
  unfold tailWord_1771223
  simp only [CollatzResearch.WordTrace]
  refine ⟨64601810062169046650190323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43067873374779364433460215 64601810062169046650190323)
  ·
    refine ⟨96902715093253569975285485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64601810062169046650190323 96902715093253569975285485)
    ·
      refine ⟨36338518159970088740732057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96902715093253569975285485 36338518159970088740732057)
      ·
        refine ⟨27253888619977566555549043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36338518159970088740732057 27253888619977566555549043)
        ·
          refine ⟨40880832929966349833323565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27253888619977566555549043 40880832929966349833323565)
          ·
            refine ⟨15330312348737381187496337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40880832929966349833323565 15330312348737381187496337)
            ·
              refine ⟨11497734261553035890622253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15330312348737381187496337 11497734261553035890622253)
              ·
                refine ⟨4311650348082388458983345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11497734261553035890622253 4311650348082388458983345)
                ·
                  refine ⟨3233737761061791344237509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4311650348082388458983345 3233737761061791344237509)
                  ·
                    refine ⟨606325830199085877044533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3233737761061791344237509 606325830199085877044533)
                    ·
                      rfl

theorem cell22_1771223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3, 2, 4].length) (baseStart_1771223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1771223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1771223 prefixEnd_1771223 := by exact prefixLift 1771223
  have htrace : WordTrace (prefixWord ++ tailWord_1771223) baseStart_1771223 baseEnd_1771223 := by
    simpa [prefixWord, tailWord_1771223, baseEnd_1771223] using wordTrace_append hprefix tailTrace_1771223
  have hstable : (prefixWord ++ tailWord_1771223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771223).length < 2 ^ (prefixWord ++ tailWord_1771223).sum := by decide
  have hdescent : baseEnd_1771223 < baseStart_1771223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771240 : List Nat := [2, 1, 4, 1, 3, 2, 1, 2, 2, 4]
def baseStart_1771240 : Nat := 118140960795 + 1771240 * 2 ^ 59
def prefixEnd_1771240 : Nat := 4983230072969 + 3 ^ 40 * 1771240 * 2
def baseEnd_1771240 : Nat := 606331649646503499369481

theorem tailTrace_1771240 : CollatzResearch.WordTrace tailWord_1771240 prefixEnd_1771240 606331649646503499369481 := by
  unfold tailWord_1771240
  simp only [CollatzResearch.WordTrace]
  refine ⟨32301215051553729276779587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43068286735404972369039449 32301215051553729276779587)
  ·
    refine ⟨48451822577330593915169381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32301215051553729276779587 48451822577330593915169381)
    ·
      refine ⟨9084716733249486359094259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48451822577330593915169381 9084716733249486359094259)
      ·
        refine ⟨13627075099874229538641389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9084716733249486359094259 13627075099874229538641389)
        ·
          refine ⟨5110153162452836076990521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13627075099874229538641389 5110153162452836076990521)
          ·
            refine ⟨3832614871839627057742891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5110153162452836076990521 3832614871839627057742891)
            ·
              refine ⟨5748922307759440586614337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3832614871839627057742891 5748922307759440586614337)
              ·
                refine ⟨4311691730819580439960753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5748922307759440586614337 4311691730819580439960753)
                ·
                  refine ⟨3233768798114685329970565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4311691730819580439960753 3233768798114685329970565)
                  ·
                    refine ⟨606331649646503499369481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3233768798114685329970565 606331649646503499369481)
                    ·
                      rfl

theorem cell22_1771240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_1771240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1771240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1771240 prefixEnd_1771240 := by exact prefixLift 1771240
  have htrace : WordTrace (prefixWord ++ tailWord_1771240) baseStart_1771240 baseEnd_1771240 := by
    simpa [prefixWord, tailWord_1771240, baseEnd_1771240] using wordTrace_append hprefix tailTrace_1771240
  have hstable : (prefixWord ++ tailWord_1771240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771240).length < 2 ^ (prefixWord ++ tailWord_1771240).sum := by decide
  have hdescent : baseEnd_1771240 < baseStart_1771240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771300 : List Nat := [2, 3, 1, 3, 2, 1, 1, 4, 5]
def baseStart_1771300 : Nat := 118140960795 + 1771300 * 2 ^ 59
def prefixEnd_1771300 : Nat := 4983230072969 + 3 ^ 40 * 1771300 * 2
def baseEnd_1771300 : Nat := 202117396290894447623099

theorem tailTrace_1771300 : CollatzResearch.WordTrace tailWord_1771300 prefixEnd_1771300 202117396290894447623099 := by
  unfold tailWord_1771300
  simp only [CollatzResearch.WordTrace]
  refine ⟨32302309241445044400371677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43069745655260059200495569 32302309241445044400371677)
  ·
    refine ⟨12113365965541891650139379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32302309241445044400371677 12113365965541891650139379)
    ·
      refine ⟨18170048948312837475209069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12113365965541891650139379 18170048948312837475209069)
      ·
        refine ⟨6813768355617314053203401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18170048948312837475209069 6813768355617314053203401)
        ·
          refine ⟨5110326266712985539902551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6813768355617314053203401 5110326266712985539902551)
          ·
            refine ⟨7665489400069478309853827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5110326266712985539902551 7665489400069478309853827)
            ·
              refine ⟨11498234100104217464780741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7665489400069478309853827 11498234100104217464780741)
              ·
                refine ⟨2155918893769540774646389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11498234100104217464780741 2155918893769540774646389)
                ·
                  refine ⟨202117396290894447623099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2155918893769540774646389 202117396290894447623099)
                  ·
                    rfl

theorem cell22_1771300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 4, 5].length) (baseStart_1771300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1771300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1771300 prefixEnd_1771300 := by exact prefixLift 1771300
  have htrace : WordTrace (prefixWord ++ tailWord_1771300) baseStart_1771300 baseEnd_1771300 := by
    simpa [prefixWord, tailWord_1771300, baseEnd_1771300] using wordTrace_append hprefix tailTrace_1771300
  have hstable : (prefixWord ++ tailWord_1771300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771300).length < 2 ^ (prefixWord ++ tailWord_1771300).sum := by decide
  have hdescent : baseEnd_1771300 < baseStart_1771300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771304 : List Nat := [2, 1, 5, 1, 1, 3, 1, 4, 1, 3]
def baseStart_1771304 : Nat := 118140960795 + 1771304 * 2 ^ 59
def prefixEnd_1771304 : Nat := 4983230072969 + 3 ^ 40 * 1771304 * 2
def baseEnd_1771304 : Nat := 606353558154428665769285

theorem tailTrace_1771304 : CollatzResearch.WordTrace tailWord_1771304 prefixEnd_1771304 606353558154428665769285 := by
  unfold tailWord_1771304
  simp only [CollatzResearch.WordTrace]
  refine ⟨32302382187437798741944483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43069842916583731655925977 32302382187437798741944483)
  ·
    refine ⟨48453573281156698112916725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32302382187437798741944483 48453573281156698112916725)
    ·
      refine ⟨4542522495108440448085943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48453573281156698112916725 4542522495108440448085943)
      ·
        refine ⟨6813783742662660672128915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4542522495108440448085943 6813783742662660672128915)
        ·
          refine ⟨10220675613993991008193373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6813783742662660672128915 10220675613993991008193373)
          ·
            refine ⟨3832753355247746628072515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10220675613993991008193373 3832753355247746628072515)
            ·
              refine ⟨5749130032871619942108773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3832753355247746628072515 5749130032871619942108773)
              ·
                refine ⟨1077961881163428739145395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5749130032871619942108773 1077961881163428739145395)
                ·
                  refine ⟨1616942821745143108718093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1077961881163428739145395 1616942821745143108718093)
                  ·
                    refine ⟨606353558154428665769285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1616942821745143108718093 606353558154428665769285)
                    ·
                      rfl

theorem cell22_1771304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_1771304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1771304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1771304 prefixEnd_1771304 := by exact prefixLift 1771304
  have htrace : WordTrace (prefixWord ++ tailWord_1771304) baseStart_1771304 baseEnd_1771304 := by
    simpa [prefixWord, tailWord_1771304, baseEnd_1771304] using wordTrace_append hprefix tailTrace_1771304
  have hstable : (prefixWord ++ tailWord_1771304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771304).length < 2 ^ (prefixWord ++ tailWord_1771304).sum := by decide
  have hdescent : baseEnd_1771304 < baseStart_1771304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771315 : List Nat := [1, 1, 1, 2, 7, 1, 1, 1, 2, 5]
def baseStart_1771315 : Nat := 118140960795 + 1771315 * 2 ^ 59
def prefixEnd_1771315 : Nat := 4983230072969 + 3 ^ 40 * 1771315 * 2
def baseEnd_1771315 : Nat := 606357323679228303744251

theorem tailTrace_1771315 : CollatzResearch.WordTrace tailWord_1771315 prefixEnd_1771315 606357323679228303744251 := by
  unfold tailWord_1771315
  simp only [CollatzResearch.WordTrace]
  refine ⟨64605165577835746362539399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43070110385223830908359599 64605165577835746362539399)
  ·
    refine ⟨96907748366753619543809099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64605165577835746362539399 96907748366753619543809099)
    ·
      refine ⟨145361622550130429315713649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96907748366753619543809099 145361622550130429315713649)
      ·
        refine ⟨109021216912597821986785237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145361622550130429315713649 109021216912597821986785237)
        ·
          refine ⟨2555184771389011452815279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 109021216912597821986785237 2555184771389011452815279)
          ·
            refine ⟨3832777157083517179222919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2555184771389011452815279 3832777157083517179222919)
            ·
              refine ⟨5749165735625275768834379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3832777157083517179222919 5749165735625275768834379)
              ·
                refine ⟨8623748603437913653251569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5749165735625275768834379 8623748603437913653251569)
                ·
                  refine ⟨6467811452578435239938677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8623748603437913653251569 6467811452578435239938677)
                  ·
                    refine ⟨606357323679228303744251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6467811452578435239938677 606357323679228303744251)
                    ·
                      rfl

theorem cell22_1771315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 2, 5].length) (baseStart_1771315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1771315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1771315 prefixEnd_1771315 := by exact prefixLift 1771315
  have htrace : WordTrace (prefixWord ++ tailWord_1771315) baseStart_1771315 baseEnd_1771315 := by
    simpa [prefixWord, tailWord_1771315, baseEnd_1771315] using wordTrace_append hprefix tailTrace_1771315
  have hstable : (prefixWord ++ tailWord_1771315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771315).length < 2 ^ (prefixWord ++ tailWord_1771315).sum := by decide
  have hdescent : baseEnd_1771315 < baseStart_1771315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771362 : List Nat := [3, 3, 2, 1, 2, 2, 2, 1, 6]
def baseStart_1771362 : Nat := 118140960795 + 1771362 * 2 ^ 59
def prefixEnd_1771362 : Nat := 4983230072969 + 3 ^ 40 * 1771362 * 2
def baseEnd_1771362 : Nat := 202124470913245282606369

theorem tailTrace_1771362 : CollatzResearch.WordTrace tailWord_1771362 prefixEnd_1771362 202124470913245282606369 := by
  unfold tailWord_1771362
  simp only [CollatzResearch.WordTrace]
  refine ⟨16151719952166368347375085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43071253205776982259666893 16151719952166368347375085)
  ·
    refine ⟨6056894982062388130265657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16151719952166368347375085 6056894982062388130265657)
    ·
      refine ⟨4542671236546791097699243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6056894982062388130265657 4542671236546791097699243)
      ·
        refine ⟨6814006854820186646548865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4542671236546791097699243 6814006854820186646548865)
        ·
          refine ⟨5110505141115139984911649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6814006854820186646548865 5110505141115139984911649)
          ·
            refine ⟨3832878855836354988683737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5110505141115139984911649 3832878855836354988683737)
            ·
              refine ⟨2874659141877266241512803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3832878855836354988683737 2874659141877266241512803)
              ·
                refine ⟨4311988712815899362269205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2874659141877266241512803 4311988712815899362269205)
                ·
                  refine ⟨202124470913245282606369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4311988712815899362269205 202124470913245282606369)
                  ·
                    rfl

theorem cell22_1771362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_1771362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1771362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1771362 prefixEnd_1771362 := by exact prefixLift 1771362
  have htrace : WordTrace (prefixWord ++ tailWord_1771362) baseStart_1771362 baseEnd_1771362 := by
    simpa [prefixWord, tailWord_1771362, baseEnd_1771362] using wordTrace_append hprefix tailTrace_1771362
  have hstable : (prefixWord ++ tailWord_1771362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771362).length < 2 ^ (prefixWord ++ tailWord_1771362).sum := by decide
  have hdescent : baseEnd_1771362 < baseStart_1771362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771403 : List Nat := [1, 1, 1, 1, 4, 2, 1, 2, 1, 8]
def baseStart_1771403 : Nat := 118140960795 + 1771403 * 2 ^ 59
def prefixEnd_1771403 : Nat := 4983230072969 + 3 ^ 40 * 1771403 * 2
def baseEnd_1771403 : Nat := 606387447877625407543981

theorem tailTrace_1771403 : CollatzResearch.WordTrace tailWord_1771403 prefixEnd_1771403 606387447877625407543981 := by
  unfold tailWord_1771403
  simp only [CollatzResearch.WordTrace]
  refine ⟨64608375201516937391742863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43072250134344624927828575 64608375201516937391742863)
  ·
    refine ⟨96912562802275406087614295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64608375201516937391742863 96912562802275406087614295)
    ·
      refine ⟨145368844203413109131421443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96912562802275406087614295 145368844203413109131421443)
      ·
        refine ⟨218053266305119663697132165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145368844203413109131421443 218053266305119663697132165)
        ·
          refine ⟨40884987432209936943212281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 218053266305119663697132165 40884987432209936943212281)
          ·
            refine ⟨30663740574157452707409211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40884987432209936943212281 30663740574157452707409211)
            ·
              refine ⟨45995610861236179061113817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30663740574157452707409211 45995610861236179061113817)
              ·
                refine ⟨34496708145927134295835363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45995610861236179061113817 34496708145927134295835363)
                ·
                  refine ⟨51745062218890701443753045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34496708145927134295835363 51745062218890701443753045)
                  ·
                    refine ⟨606387447877625407543981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 51745062218890701443753045 606387447877625407543981)
                    ·
                      rfl

theorem cell22_1771403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 8].length) (baseStart_1771403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1771403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1771403 prefixEnd_1771403 := by exact prefixLift 1771403
  have htrace : WordTrace (prefixWord ++ tailWord_1771403) baseStart_1771403 baseEnd_1771403 := by
    simpa [prefixWord, tailWord_1771403, baseEnd_1771403] using wordTrace_append hprefix tailTrace_1771403
  have hstable : (prefixWord ++ tailWord_1771403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771403).length < 2 ^ (prefixWord ++ tailWord_1771403).sum := by decide
  have hdescent : baseEnd_1771403 < baseStart_1771403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771480 : List Nat := [2, 1, 2, 2, 2, 2, 2, 3, 6]
def baseStart_1771480 : Nat := 118140960795 + 1771480 * 2 ^ 59
def prefixEnd_1771480 : Nat := 4983230072969 + 3 ^ 40 * 1771480 * 2
def baseEnd_1771480 : Nat := 202137935517074291122915

theorem tailTrace_1771480 : CollatzResearch.WordTrace tailWord_1771480 prefixEnd_1771480 202137935517074291122915 := by
  unfold tailWord_1771480
  simp only [CollatzResearch.WordTrace]
  refine ⟨32305591811118989771147947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43074122414825319694863929 32305591811118989771147947)
  ·
    refine ⟨48458387716678484656721921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32305591811118989771147947 48458387716678484656721921)
    ·
      refine ⟨36343790787508863492541441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48458387716678484656721921 36343790787508863492541441)
      ·
        refine ⟨27257843090631647619406081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36343790787508863492541441 27257843090631647619406081)
        ·
          refine ⟨20443382317973735714554561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27257843090631647619406081 20443382317973735714554561)
          ·
            refine ⟨15332536738480301785915921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20443382317973735714554561 15332536738480301785915921)
            ·
              refine ⟨11499402553860226339436941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15332536738480301785915921 11499402553860226339436941)
              ·
                refine ⟨4312275957697584877288853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11499402553860226339436941 4312275957697584877288853)
                ·
                  refine ⟨202137935517074291122915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4312275957697584877288853 202137935517074291122915)
                  ·
                    rfl

theorem cell22_1771480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3, 6].length) (baseStart_1771480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1771480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1771480 prefixEnd_1771480 := by exact prefixLift 1771480
  have htrace : WordTrace (prefixWord ++ tailWord_1771480) baseStart_1771480 baseEnd_1771480 := by
    simpa [prefixWord, tailWord_1771480, baseEnd_1771480] using wordTrace_append hprefix tailTrace_1771480
  have hstable : (prefixWord ++ tailWord_1771480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771480).length < 2 ^ (prefixWord ++ tailWord_1771480).sum := by decide
  have hdescent : baseEnd_1771480 < baseStart_1771480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771525 : List Nat := [1, 3, 1, 1, 2, 5, 9]
def baseStart_1771525 : Nat := 118140960795 + 1771525 * 2 ^ 59
def prefixEnd_1771525 : Nat := 4983230072969 + 3 ^ 40 * 1771525 * 2
def baseEnd_1771525 : Nat := 22460341147068805777541

theorem tailTrace_1771525 : CollatzResearch.WordTrace tailWord_1771525 prefixEnd_1771525 22460341147068805777541 := by
  unfold tailWord_1771525
  simp only [CollatzResearch.WordTrace]
  refine ⟨64612824907074952227684029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43075216604716634818456019 64612824907074952227684029)
  ·
    refine ⟨24229809340153107085381511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64612824907074952227684029 24229809340153107085381511)
    ·
      refine ⟨36344714010229660628072267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24229809340153107085381511 36344714010229660628072267)
      ·
        refine ⟨54517071015344490942108401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36344714010229660628072267 54517071015344490942108401)
        ·
          refine ⟨40887803261508368206581301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54517071015344490942108401 40887803261508368206581301)
          ·
            refine ⟨3833231555766409519366997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40887803261508368206581301 3833231555766409519366997)
            ·
              refine ⟨22460341147068805777541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3833231555766409519366997 22460341147068805777541)
              ·
                rfl

theorem cell22_1771525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 9].length) (baseStart_1771525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1771525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1771525 prefixEnd_1771525 := by exact prefixLift 1771525
  have htrace : WordTrace (prefixWord ++ tailWord_1771525) baseStart_1771525 baseEnd_1771525 := by
    simpa [prefixWord, tailWord_1771525, baseEnd_1771525] using wordTrace_append hprefix tailTrace_1771525
  have hstable : (prefixWord ++ tailWord_1771525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771525).length < 2 ^ (prefixWord ++ tailWord_1771525).sum := by decide
  have hdescent : baseEnd_1771525 < baseStart_1771525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771546 : List Nat := [3, 1, 1, 3, 1, 4, 3, 1, 2, 3]
def baseStart_1771546 : Nat := 118140960795 + 1771546 * 2 ^ 59
def prefixEnd_1771546 : Nat := 4983230072969 + 3 ^ 40 * 1771546 * 2
def baseEnd_1771546 : Nat := 606436399700020701218543

theorem tailTrace_1771546 : CollatzResearch.WordTrace tailWord_1771546 prefixEnd_1771546 606436399700020701218543 := by
  unfold tailWord_1771546
  simp only [CollatzResearch.WordTrace]
  refine ⟨16153397709999718203549623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43075727226665915209465661 16153397709999718203549623)
  ·
    refine ⟨24230096564999577305324435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16153397709999718203549623 24230096564999577305324435)
    ·
      refine ⟨36345144847499365957986653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24230096564999577305324435 36345144847499365957986653)
      ·
        refine ⟨13629429317812262234244995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36345144847499365957986653 13629429317812262234244995)
        ·
          refine ⟨20444143976718393351367493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13629429317812262234244995 20444143976718393351367493)
          ·
            refine ⟨3833276995634698753381405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20444143976718393351367493 3833276995634698753381405)
            ·
              refine ⟨1437478873363012032518027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3833276995634698753381405 1437478873363012032518027)
              ·
                refine ⟨2156218310044518048777041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1437478873363012032518027 2156218310044518048777041)
                ·
                  refine ⟨1617163732533388536582781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2156218310044518048777041 1617163732533388536582781)
                  ·
                    refine ⟨606436399700020701218543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1617163732533388536582781 606436399700020701218543)
                    ·
                      rfl

theorem cell22_1771546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 1, 2, 3].length) (baseStart_1771546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1771546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1771546 prefixEnd_1771546 := by exact prefixLift 1771546
  have htrace : WordTrace (prefixWord ++ tailWord_1771546) baseStart_1771546 baseEnd_1771546 := by
    simpa [prefixWord, tailWord_1771546, baseEnd_1771546] using wordTrace_append hprefix tailTrace_1771546
  have hstable : (prefixWord ++ tailWord_1771546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771546).length < 2 ^ (prefixWord ++ tailWord_1771546).sum := by decide
  have hdescent : baseEnd_1771546 < baseStart_1771546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771559 : List Nat := [1, 1, 7, 1, 2, 1, 1, 8]
def baseStart_1771559 : Nat := 118140960795 + 1771559 * 2 ^ 59
def prefixEnd_1771559 : Nat := 4983230072969 + 3 ^ 40 * 1771559 * 2
def baseEnd_1771559 : Nat := 67382316651743666738167

theorem tailTrace_1771559 : CollatzResearch.WordTrace tailWord_1771559 prefixEnd_1771559 67382316651743666738167 := by
  unfold tailWord_1771559
  simp only [CollatzResearch.WordTrace]
  refine ⟨64614064988951776034421731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43076043325967850689614487 64614064988951776034421731)
  ·
    refine ⟨96921097483427664051632597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64614064988951776034421731 96921097483427664051632597)
    ·
      refine ⟨2271588222267835876210139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 96921097483427664051632597 2271588222267835876210139)
      ·
        refine ⟨3407382333401753814315209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2271588222267835876210139 3407382333401753814315209)
        ·
          refine ⟨2555536750051315360736407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3407382333401753814315209 2555536750051315360736407)
          ·
            refine ⟨3833305125076973041104611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2555536750051315360736407 3833305125076973041104611)
            ·
              refine ⟨5749957687615459561656917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3833305125076973041104611 5749957687615459561656917)
              ·
                refine ⟨67382316651743666738167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5749957687615459561656917 67382316651743666738167)
                ·
                  rfl

theorem cell22_1771559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 8].length) (baseStart_1771559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1771559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1771559 prefixEnd_1771559 := by exact prefixLift 1771559
  have htrace : WordTrace (prefixWord ++ tailWord_1771559) baseStart_1771559 baseEnd_1771559 := by
    simpa [prefixWord, tailWord_1771559, baseEnd_1771559] using wordTrace_append hprefix tailTrace_1771559
  have hstable : (prefixWord ++ tailWord_1771559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771559).length < 2 ^ (prefixWord ++ tailWord_1771559).sum := by decide
  have hdescent : baseEnd_1771559 < baseStart_1771559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771600 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 1, 10]
def baseStart_1771600 : Nat := 118140960795 + 1771600 * 2 ^ 59
def prefixEnd_1771600 : Nat := 4983230072969 + 3 ^ 40 * 1771600 * 2
def baseEnd_1771600 : Nat := 606454885003582560368377

theorem tailTrace_1771600 : CollatzResearch.WordTrace tailWord_1771600 prefixEnd_1771600 606454885003582560368377 := by
  unfold tailWord_1771600
  simp only [CollatzResearch.WordTrace]
  refine ⟨32307780190901620018332127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43077040254535493357776169 32307780190901620018332127)
  ·
    refine ⟨48461670286352430027498191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32307780190901620018332127 48461670286352430027498191)
    ·
      refine ⟨72692505429528645041247287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48461670286352430027498191 72692505429528645041247287)
      ·
        refine ⟨109038758144292967561870931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72692505429528645041247287 109038758144292967561870931)
        ·
          refine ⟨163558137216439451342806397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109038758144292967561870931 163558137216439451342806397)
          ·
            refine ⟨61334301456164794253552399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163558137216439451342806397 61334301456164794253552399)
            ·
              refine ⟨92001452184247191380328599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61334301456164794253552399 92001452184247191380328599)
              ·
                refine ⟨138002178276370787070492899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92001452184247191380328599 138002178276370787070492899)
                ·
                  refine ⟨207003267414556180605739349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138002178276370787070492899 207003267414556180605739349)
                  ·
                    refine ⟨606454885003582560368377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 207003267414556180605739349 606454885003582560368377)
                    ·
                      rfl

theorem cell22_1771600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 1, 10].length) (baseStart_1771600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1771600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1771600 prefixEnd_1771600 := by exact prefixLift 1771600
  have htrace : WordTrace (prefixWord ++ tailWord_1771600) baseStart_1771600 baseEnd_1771600 := by
    simpa [prefixWord, tailWord_1771600, baseEnd_1771600] using wordTrace_append hprefix tailTrace_1771600
  have hstable : (prefixWord ++ tailWord_1771600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771600).length < 2 ^ (prefixWord ++ tailWord_1771600).sum := by decide
  have hdescent : baseEnd_1771600 < baseStart_1771600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771664 : List Nat := [2, 1, 1, 1, 1, 1, 5, 5, 2, 3]
def baseStart_1771664 : Nat := 118140960795 + 1771664 * 2 ^ 59
def prefixEnd_1771664 : Nat := 4983230072969 + 3 ^ 40 * 1771664 * 2
def baseEnd_1771664 : Nat := 606476793511507726768181

theorem tailTrace_1771664 : CollatzResearch.WordTrace tailWord_1771664 prefixEnd_1771664 606476793511507726768181 := by
  unfold tailWord_1771664
  simp only [CollatzResearch.WordTrace]
  refine ⟨32308947326785689483497023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43078596435714252644662697 32308947326785689483497023)
  ·
    refine ⟨48463420990178534225245535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32308947326785689483497023 48463420990178534225245535)
    ·
      refine ⟨72695131485267801337868303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48463420990178534225245535 72695131485267801337868303)
      ·
        refine ⟨109042697227901702006802455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72695131485267801337868303 109042697227901702006802455)
        ·
          refine ⟨163564045841852553010203683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109042697227901702006802455 163564045841852553010203683)
          ·
            refine ⟨245346068762778829515305525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163564045841852553010203683 245346068762778829515305525)
            ·
              refine ⟨23001193946510515267059893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 245346068762778829515305525 23001193946510515267059893)
              ·
                refine ⟨2156361932485360806286865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23001193946510515267059893 2156361932485360806286865)
                ·
                  refine ⟨1617271449364020604715149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2156361932485360806286865 1617271449364020604715149)
                  ·
                    refine ⟨606476793511507726768181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1617271449364020604715149 606476793511507726768181)
                    ·
                      rfl

theorem cell22_1771664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 5, 2, 3].length) (baseStart_1771664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1771664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1771664 prefixEnd_1771664 := by exact prefixLift 1771664
  have htrace : WordTrace (prefixWord ++ tailWord_1771664) baseStart_1771664 baseEnd_1771664 := by
    simpa [prefixWord, tailWord_1771664, baseEnd_1771664] using wordTrace_append hprefix tailTrace_1771664
  have hstable : (prefixWord ++ tailWord_1771664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771664).length < 2 ^ (prefixWord ++ tailWord_1771664).sum := by decide
  have hdescent : baseEnd_1771664 < baseStart_1771664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771679 : List Nat := [1, 1, 2, 6, 1, 2, 1, 1, 1, 6]
def baseStart_1771679 : Nat := 118140960795 + 1771679 * 2 ^ 59
def prefixEnd_1771679 : Nat := 4983230072969 + 3 ^ 40 * 1771679 * 2
def baseEnd_1771679 : Nat := 606481928318052687643135

theorem tailTrace_1771679 : CollatzResearch.WordTrace tailWord_1771679 prefixEnd_1771679 606481928318052687643135 := by
  unfold tailWord_1771679
  simp only [CollatzResearch.WordTrace]
  refine ⟨64618441748517036528790091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43078961165678024352526727 64618441748517036528790091)
  ·
    refine ⟨96927662622775554793185137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64618441748517036528790091 96927662622775554793185137)
    ·
      refine ⟨72695746967081666094888853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96927662622775554793185137 72695746967081666094888853)
      ·
        refine ⟨3407613139081953098197915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 72695746967081666094888853 3407613139081953098197915)
        ·
          refine ⟨5111419708622929647296873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3407613139081953098197915 5111419708622929647296873)
          ·
            refine ⟨3833564781467197235472655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5111419708622929647296873 3833564781467197235472655)
            ·
              refine ⟨5750347172200795853208983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3833564781467197235472655 5750347172200795853208983)
              ·
                refine ⟨8625520758301193779813475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5750347172200795853208983 8625520758301193779813475)
                ·
                  refine ⟨12938281137451790669720213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8625520758301193779813475 12938281137451790669720213)
                  ·
                    refine ⟨606481928318052687643135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12938281137451790669720213 606481928318052687643135)
                    ·
                      rfl

theorem cell22_1771679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 6].length) (baseStart_1771679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1771679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1771679 prefixEnd_1771679 := by exact prefixLift 1771679
  have htrace : WordTrace (prefixWord ++ tailWord_1771679) baseStart_1771679 baseEnd_1771679 := by
    simpa [prefixWord, tailWord_1771679, baseEnd_1771679] using wordTrace_append hprefix tailTrace_1771679
  have hstable : (prefixWord ++ tailWord_1771679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771679).length < 2 ^ (prefixWord ++ tailWord_1771679).sum := by decide
  have hdescent : baseEnd_1771679 < baseStart_1771679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771700 : List Nat := [2, 5, 3, 1, 1, 1, 2, 1, 6]
def baseStart_1771700 : Nat := 118140960795 + 1771700 * 2 ^ 59
def prefixEnd_1771700 : Nat := 4983230072969 + 3 ^ 40 * 1771700 * 2
def baseEnd_1771700 : Nat := 202163039015738544289357

theorem tailTrace_1771700 : CollatzResearch.WordTrace tailWord_1771700 prefixEnd_1771700 202163039015738544289357 := by
  unfold tailWord_1771700
  simp only [CollatzResearch.WordTrace]
  refine ⟨32309603840720478557652277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43079471787627304743536369 32309603840720478557652277)
  ·
    refine ⟨3029025360067544864779901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32309603840720478557652277 3029025360067544864779901)
    ·
      refine ⟨1135884510025329324292463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3029025360067544864779901 1135884510025329324292463)
      ·
        refine ⟨1703826765037993986438695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1135884510025329324292463 1703826765037993986438695)
        ·
          refine ⟨2555740147556990979658043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1703826765037993986438695 2555740147556990979658043)
          ·
            refine ⟨3833610221335486469487065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2555740147556990979658043 3833610221335486469487065)
            ·
              refine ⟨2875207666001614852115299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3833610221335486469487065 2875207666001614852115299)
              ·
                refine ⟨4312811499002422278172949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2875207666001614852115299 4312811499002422278172949)
                ·
                  refine ⟨202163039015738544289357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4312811499002422278172949 202163039015738544289357)
                  ·
                    rfl

theorem cell22_1771700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_1771700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1771700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1771700 prefixEnd_1771700 := by exact prefixLift 1771700
  have htrace : WordTrace (prefixWord ++ tailWord_1771700) baseStart_1771700 baseEnd_1771700 := by
    simpa [prefixWord, tailWord_1771700, baseEnd_1771700] using wordTrace_append hprefix tailTrace_1771700
  have hstable : (prefixWord ++ tailWord_1771700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771700).length < 2 ^ (prefixWord ++ tailWord_1771700).sum := by decide
  have hdescent : baseEnd_1771700 < baseStart_1771700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771726 : List Nat := [4, 1, 1, 1, 4, 1, 2, 2, 3, 3]
def baseStart_1771726 : Nat := 118140960795 + 1771726 * 2 ^ 59
def prefixEnd_1771726 : Nat := 4983230072969 + 3 ^ 40 * 1771726 * 2
def baseEnd_1771726 : Nat := 606498017378560231717991

theorem tailTrace_1771726 : CollatzResearch.WordTrace tailWord_1771726 prefixEnd_1771726 606498017378560231717991 := by
  unfold tailWord_1771726
  simp only [CollatzResearch.WordTrace]
  refine ⟨8077519497418345444468879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43080103986231175703834021 8077519497418345444468879)
  ·
    refine ⟨12116279246127518166703319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8077519497418345444468879 12116279246127518166703319)
    ·
      refine ⟨18174418869191277250054979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12116279246127518166703319 18174418869191277250054979)
      ·
        refine ⟨27261628303786915875082469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18174418869191277250054979 27261628303786915875082469)
        ·
          refine ⟨5111555306960046726577963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27261628303786915875082469 5111555306960046726577963)
          ·
            refine ⟨7667332960440070089866945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5111555306960046726577963 7667332960440070089866945)
            ·
              refine ⟨5750499720330052567400209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7667332960440070089866945 5750499720330052567400209)
              ·
                refine ⟨4312874790247539425550157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5750499720330052567400209 4312874790247539425550157)
                ·
                  refine ⟨1617328046342827284581309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4312874790247539425550157 1617328046342827284581309)
                  ·
                    refine ⟨606498017378560231717991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1617328046342827284581309 606498017378560231717991)
                    ·
                      rfl

theorem cell22_1771726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2, 3, 3].length) (baseStart_1771726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1771726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1771726 prefixEnd_1771726 := by exact prefixLift 1771726
  have htrace : WordTrace (prefixWord ++ tailWord_1771726) baseStart_1771726 baseEnd_1771726 := by
    simpa [prefixWord, tailWord_1771726, baseEnd_1771726] using wordTrace_append hprefix tailTrace_1771726
  have hstable : (prefixWord ++ tailWord_1771726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771726).length < 2 ^ (prefixWord ++ tailWord_1771726).sum := by decide
  have hdescent : baseEnd_1771726 < baseStart_1771726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771737 : List Nat := [1, 2, 1, 2, 3, 1, 2, 2, 1, 7]
def baseStart_1771737 : Nat := 118140960795 + 1771737 * 2 ^ 59
def prefixEnd_1771737 : Nat := 4983230072969 + 3 ^ 40 * 1771737 * 2
def baseEnd_1771737 : Nat := 606501782903359869692957

theorem tailTrace_1771737 : CollatzResearch.WordTrace tailWord_1771737 prefixEnd_1771737 606501782903359869692957 := by
  unfold tailWord_1771737
  simp only [CollatzResearch.WordTrace]
  refine ⟨64620557182306912434401465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43080371454871274956267643 64620557182306912434401465)
  ·
    refine ⟨48465417886730184325801099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64620557182306912434401465 48465417886730184325801099)
    ·
      refine ⟨72698126830095276488701649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48465417886730184325801099 72698126830095276488701649)
      ·
        refine ⟨54523595122571457366526237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72698126830095276488701649 54523595122571457366526237)
        ·
          refine ⟨20446348170964296512447339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54523595122571457366526237 20446348170964296512447339)
          ·
            refine ⟨30669522256446444768671009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20446348170964296512447339 30669522256446444768671009)
            ·
              refine ⟨23002141692334833576503257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30669522256446444768671009 23002141692334833576503257)
              ·
                refine ⟨17251606269251125182377443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23002141692334833576503257 17251606269251125182377443)
                ·
                  refine ⟨25877409403876687773566165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17251606269251125182377443 25877409403876687773566165)
                  ·
                    refine ⟨606501782903359869692957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25877409403876687773566165 606501782903359869692957)
                    ·
                      rfl

theorem cell22_1771737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 7].length) (baseStart_1771737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1771737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1771737 prefixEnd_1771737 := by exact prefixLift 1771737
  have htrace : WordTrace (prefixWord ++ tailWord_1771737) baseStart_1771737 baseEnd_1771737 := by
    simpa [prefixWord, tailWord_1771737, baseEnd_1771737] using wordTrace_append hprefix tailTrace_1771737
  have hstable : (prefixWord ++ tailWord_1771737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771737).length < 2 ^ (prefixWord ++ tailWord_1771737).sum := by decide
  have hdescent : baseEnd_1771737 < baseStart_1771737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771786 : List Nat := [3, 1, 2, 2, 1, 1, 5, 2, 1, 4]
def baseStart_1771786 : Nat := 118140960795 + 1771786 * 2 ^ 59
def prefixEnd_1771786 : Nat := 4983230072969 + 3 ^ 40 * 1771786 * 2
def baseEnd_1771786 : Nat := 606518556604740075217807

theorem tailTrace_1771786 : CollatzResearch.WordTrace tailWord_1771786 prefixEnd_1771786 606518556604740075217807 := by
  unfold tailWord_1771786
  simp only [CollatzResearch.WordTrace]
  refine ⟨16155586089782348450733803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43081562906086262535290141 16155586089782348450733803)
  ·
    refine ⟨24233379134673522676100705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16155586089782348450733803 24233379134673522676100705)
    ·
      refine ⟨18175034351005142007075529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24233379134673522676100705 18175034351005142007075529)
      ·
        refine ⟨13631275763253856505306647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18175034351005142007075529 13631275763253856505306647)
        ·
          refine ⟨20446913644880784757959971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13631275763253856505306647 20446913644880784757959971)
          ·
            refine ⟨30670370467321177136939957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20446913644880784757959971 30670370467321177136939957)
            ·
              refine ⟨2875347231311360356588121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30670370467321177136939957 2875347231311360356588121)
              ·
                refine ⟨2156510423483520267441091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2875347231311360356588121 2156510423483520267441091)
                ·
                  refine ⟨3234765635225280401161637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2156510423483520267441091 3234765635225280401161637)
                  ·
                    refine ⟨606518556604740075217807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3234765635225280401161637 606518556604740075217807)
                    ·
                      rfl

theorem cell22_1771786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 2, 1, 4].length) (baseStart_1771786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1771786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1771786 prefixEnd_1771786 := by exact prefixLift 1771786
  have htrace : WordTrace (prefixWord ++ tailWord_1771786) baseStart_1771786 baseEnd_1771786 := by
    simpa [prefixWord, tailWord_1771786, baseEnd_1771786] using wordTrace_append hprefix tailTrace_1771786
  have hstable : (prefixWord ++ tailWord_1771786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771786).length < 2 ^ (prefixWord ++ tailWord_1771786).sum := by decide
  have hdescent : baseEnd_1771786 < baseStart_1771786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771799 : List Nat := [1, 1, 3, 4, 1, 2, 1, 1, 3, 5]
def baseStart_1771799 : Nat := 118140960795 + 1771799 * 2 ^ 59
def prefixEnd_1771799 : Nat := 4983230072969 + 3 ^ 40 * 1771799 * 2
def baseEnd_1771799 : Nat := 606523006770412374642767

theorem tailTrace_1771799 : CollatzResearch.WordTrace tailWord_1771799 prefixEnd_1771799 606523006770412374642767 := by
  unfold tailWord_1771799
  simp only [CollatzResearch.WordTrace]
  refine ⟨64622818508082297023158451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43081879005388198015438967 64622818508082297023158451)
  ·
    refine ⟨96934227762123445534737677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64622818508082297023158451 96934227762123445534737677)
    ·
      refine ⟨36350335410796292075526629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96934227762123445534737677 36350335410796292075526629)
      ·
        refine ⟨6815687889524304764161243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36350335410796292075526629 6815687889524304764161243)
        ·
          refine ⟨10223531834286457146241865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6815687889524304764161243 10223531834286457146241865)
          ·
            refine ⟨7667648875714842859681399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10223531834286457146241865 7667648875714842859681399)
            ·
              refine ⟨11501473313572264289522099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7667648875714842859681399 11501473313572264289522099)
              ·
                refine ⟨17252209970358396434283149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11501473313572264289522099 17252209970358396434283149)
                ·
                  refine ⟨6469578738884398662856181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17252209970358396434283149 6469578738884398662856181)
                  ·
                    refine ⟨606523006770412374642767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6469578738884398662856181 606523006770412374642767)
                    ·
                      rfl

theorem cell22_1771799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 3, 5].length) (baseStart_1771799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1771799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1771799 prefixEnd_1771799 := by exact prefixLift 1771799
  have htrace : WordTrace (prefixWord ++ tailWord_1771799) baseStart_1771799 baseEnd_1771799 := by
    simpa [prefixWord, tailWord_1771799, baseEnd_1771799] using wordTrace_append hprefix tailTrace_1771799
  have hstable : (prefixWord ++ tailWord_1771799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771799).length < 2 ^ (prefixWord ++ tailWord_1771799).sum := by decide
  have hdescent : baseEnd_1771799 < baseStart_1771799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771833 : List Nat := [1, 2, 1, 6, 1, 1, 2, 3, 2, 3]
def baseStart_1771833 : Nat := 118140960795 + 1771833 * 2 ^ 59
def prefixEnd_1771833 : Nat := 4983230072969 + 3 ^ 40 * 1771833 * 2
def baseEnd_1771833 : Nat := 606534645665247619292663

theorem tailTrace_1771833 : CollatzResearch.WordTrace tailWord_1771833 prefixEnd_1771833 606534645665247619292663 := by
  unfold tailWord_1771833
  simp only [CollatzResearch.WordTrace]
  refine ⟨64624058589959120829896153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43082705726639413886597435 64624058589959120829896153)
  ·
    refine ⟨48468043942469340622422115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64624058589959120829896153 48468043942469340622422115)
    ·
      refine ⟨72702065913704010933633173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48468043942469340622422115 72702065913704010933633173)
      ·
        refine ⟨3407909339704875512514055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 72702065913704010933633173 3407909339704875512514055)
        ·
          refine ⟨5111864009557313268771083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3407909339704875512514055 5111864009557313268771083)
          ·
            refine ⟨7667796014335969903156625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5111864009557313268771083 7667796014335969903156625)
            ·
              refine ⟨5750847010751977427367469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7667796014335969903156625 5750847010751977427367469)
              ·
                refine ⟨2156567629031991535262801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5750847010751977427367469 2156567629031991535262801)
                ·
                  refine ⟨1617425721773993651447101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2156567629031991535262801 1617425721773993651447101)
                  ·
                    refine ⟨606534645665247619292663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1617425721773993651447101 606534645665247619292663)
                    ·
                      rfl

theorem cell22_1771833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 3, 2, 3].length) (baseStart_1771833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1771833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1771833 prefixEnd_1771833 := by exact prefixLift 1771833
  have htrace : WordTrace (prefixWord ++ tailWord_1771833) baseStart_1771833 baseEnd_1771833 := by
    simpa [prefixWord, tailWord_1771833, baseEnd_1771833] using wordTrace_append hprefix tailTrace_1771833
  have hstable : (prefixWord ++ tailWord_1771833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771833).length < 2 ^ (prefixWord ++ tailWord_1771833).sum := by decide
  have hdescent : baseEnd_1771833 < baseStart_1771833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771936 : List Nat := [2, 1, 1, 4, 1, 3, 3, 1, 6]
def baseStart_1771936 : Nat := 118140960795 + 1771936 * 2 ^ 59
def prefixEnd_1771936 : Nat := 4983230072969 + 3 ^ 40 * 1771936 * 2
def baseEnd_1771936 : Nat := 202189968223396561322449

theorem tailTrace_1771936 : CollatzResearch.WordTrace tailWord_1771936 prefixEnd_1771936 202189968223396561322449 := by
  unfold tailWord_1771936
  simp only [CollatzResearch.WordTrace]
  refine ⟨32313907654292984710447831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43085210205723979613930441 32313907654292984710447831)
  ·
    refine ⟨48470861481439477065671747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32313907654292984710447831 48470861481439477065671747)
    ·
      refine ⟨72706292222159215598507621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48470861481439477065671747 72706292222159215598507621)
      ·
        refine ⟨13632429791654852924720179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72706292222159215598507621 13632429791654852924720179)
        ·
          refine ⟨20448644687482279387080269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13632429791654852924720179 20448644687482279387080269)
          ·
            refine ⟨7668241757805854770155101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20448644687482279387080269 7668241757805854770155101)
            ·
              refine ⟨2875590659177195538808163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7668241757805854770155101 2875590659177195538808163)
              ·
                refine ⟨4313385988765793308212245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2875590659177195538808163 4313385988765793308212245)
                ·
                  refine ⟨202189968223396561322449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4313385988765793308212245 202189968223396561322449)
                  ·
                    rfl

theorem cell22_1771936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 1, 6].length) (baseStart_1771936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1771936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1771936 prefixEnd_1771936 := by exact prefixLift 1771936
  have htrace : WordTrace (prefixWord ++ tailWord_1771936) baseStart_1771936 baseEnd_1771936 := by
    simpa [prefixWord, tailWord_1771936, baseEnd_1771936] using wordTrace_append hprefix tailTrace_1771936
  have hstable : (prefixWord ++ tailWord_1771936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771936).length < 2 ^ (prefixWord ++ tailWord_1771936).sum := by decide
  have hdescent : baseEnd_1771936 < baseStart_1771936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771966 : List Nat := [4, 2, 1, 1, 1, 1, 2, 3, 1, 6]
def baseStart_1771966 : Nat := 118140960795 + 1771966 * 2 ^ 59
def prefixEnd_1771966 : Nat := 4983230072969 + 3 ^ 40 * 1771966 * 2
def baseEnd_1771966 : Nat := 606580174283279605717255

theorem tailTrace_1771966 : CollatzResearch.WordTrace tailWord_1771966 prefixEnd_1771966 606580174283279605717255 := by
  unfold tailWord_1771966
  simp only [CollatzResearch.WordTrace]
  refine ⟨8078613687309660568060969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43085939665651523029658501 8078613687309660568060969)
  ·
    refine ⟨6058960265482245426045727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8078613687309660568060969 6058960265482245426045727)
    ·
      refine ⟨9088440398223368139068591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6058960265482245426045727 9088440398223368139068591)
      ·
        refine ⟨13632660597335052208602887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9088440398223368139068591 13632660597335052208602887)
        ·
          refine ⟨20448990896002578312904331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13632660597335052208602887 20448990896002578312904331)
          ·
            refine ⟨30673486344003867469356497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20448990896002578312904331 30673486344003867469356497)
            ·
              refine ⟨23005114758002900602017373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30673486344003867469356497 23005114758002900602017373)
              ·
                refine ⟨8626918034251087725756515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23005114758002900602017373 8626918034251087725756515)
                ·
                  refine ⟨12940377051376631588634773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8626918034251087725756515 12940377051376631588634773)
                  ·
                    refine ⟨606580174283279605717255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12940377051376631588634773 606580174283279605717255)
                    ·
                      rfl

theorem cell22_1771966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_1771966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1771966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1771966 prefixEnd_1771966 := by exact prefixLift 1771966
  have htrace : WordTrace (prefixWord ++ tailWord_1771966) baseStart_1771966 baseEnd_1771966 := by
    simpa [prefixWord, tailWord_1771966, baseEnd_1771966] using wordTrace_append hprefix tailTrace_1771966
  have hstable : (prefixWord ++ tailWord_1771966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771966).length < 2 ^ (prefixWord ++ tailWord_1771966).sum := by decide
  have hdescent : baseEnd_1771966 < baseStart_1771966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771972 : List Nat := [2, 3, 3, 2, 2, 1, 3, 1, 1, 4]
def baseStart_1771972 : Nat := 118140960795 + 1771972 * 2 ^ 59
def prefixEnd_1771972 : Nat := 4983230072969 + 3 ^ 40 * 1771972 * 2
def baseEnd_1771972 : Nat := 606582228205897590067237

theorem tailTrace_1771972 : CollatzResearch.WordTrace tailWord_1771972 prefixEnd_1771972 606582228205897590067237 := by
  unfold tailWord_1771972
  simp only [CollatzResearch.WordTrace]
  refine ⟨32314564168227773784603085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43086085557637031712804113 32314564168227773784603085)
  ·
    refine ⟨12117961563085415169226157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32314564168227773784603085 12117961563085415169226157)
    ·
      refine ⟨4544235586157030688459809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12117961563085415169226157 4544235586157030688459809)
      ·
        refine ⟨3408176689617773016344857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4544235586157030688459809 3408176689617773016344857)
        ·
          refine ⟨2556132517213329762258643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3408176689617773016344857 2556132517213329762258643)
          ·
            refine ⟨3834198775819994643387965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2556132517213329762258643 3834198775819994643387965)
            ·
              refine ⟨1437824540932497991270487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3834198775819994643387965 1437824540932497991270487)
              ·
                refine ⟨2156736811398746986905731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1437824540932497991270487 2156736811398746986905731)
                ·
                  refine ⟨3235105217098120480358597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2156736811398746986905731 3235105217098120480358597)
                  ·
                    refine ⟨606582228205897590067237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3235105217098120480358597 606582228205897590067237)
                    ·
                      rfl

theorem cell22_1771972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_1771972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1771972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1771972 prefixEnd_1771972 := by exact prefixLift 1771972
  have htrace : WordTrace (prefixWord ++ tailWord_1771972) baseStart_1771972 baseEnd_1771972 := by
    simpa [prefixWord, tailWord_1771972, baseEnd_1771972] using wordTrace_append hprefix tailTrace_1771972
  have hstable : (prefixWord ++ tailWord_1771972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771972).length < 2 ^ (prefixWord ++ tailWord_1771972).sum := by decide
  have hdescent : baseEnd_1771972 < baseStart_1771972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772002 : List Nat := [3, 3, 3, 2, 1, 1, 2, 1, 1, 5]
def baseStart_1772002 : Nat := 118140960795 + 1772002 * 2 ^ 59
def prefixEnd_1772002 : Nat := 4983230072969 + 3 ^ 40 * 1772002 * 2
def baseEnd_1772002 : Nat := 606592497818987511817145

theorem tailTrace_1772002 : CollatzResearch.WordTrace tailWord_1772002 prefixEnd_1772002 606592497818987511817145 := by
  unfold tailWord_1772002
  simp only [CollatzResearch.WordTrace]
  refine ⟨16157555631586715673199565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43086815017564575128532173 16157555631586715673199565)
  ·
    refine ⟨6059083361845018377449837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16157555631586715673199565 6059083361845018377449837)
    ·
      refine ⟨2272156260691881891543689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6059083361845018377449837 2272156260691881891543689)
      ·
        refine ⟨1704117195518911418657767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2272156260691881891543689 1704117195518911418657767)
        ·
          refine ⟨2556175793278367127986651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1704117195518911418657767 2556175793278367127986651)
          ·
            refine ⟨3834263689917550691979977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2556175793278367127986651 3834263689917550691979977)
            ·
              refine ⟨2875697767438163018984983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3834263689917550691979977 2875697767438163018984983)
              ·
                refine ⟨4313546651157244528477475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2875697767438163018984983 4313546651157244528477475)
                ·
                  refine ⟨6470319976735866792716213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4313546651157244528477475 6470319976735866792716213)
                  ·
                    refine ⟨606592497818987511817145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6470319976735866792716213 606592497818987511817145)
                    ·
                      rfl

theorem cell22_1772002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_1772002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1772002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1772002 prefixEnd_1772002 := by exact prefixLift 1772002
  have htrace : WordTrace (prefixWord ++ tailWord_1772002) baseStart_1772002 baseEnd_1772002 := by
    simpa [prefixWord, tailWord_1772002, baseEnd_1772002] using wordTrace_append hprefix tailTrace_1772002
  have hstable : (prefixWord ++ tailWord_1772002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772002).length < 2 ^ (prefixWord ++ tailWord_1772002).sum := by decide
  have hdescent : baseEnd_1772002 < baseStart_1772002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772043 : List Nat := [1, 1, 1, 1, 7, 1, 3, 2, 5]
def baseStart_1772043 : Nat := 118140960795 + 1772043 * 2 ^ 59
def prefixEnd_1772043 : Nat := 4983230072969 + 3 ^ 40 * 1772043 * 2
def baseEnd_1772043 : Nat := 202202177652292357180673

theorem tailTrace_1772043 : CollatzResearch.WordTrace tailWord_1772043 prefixEnd_1772043 202202177652292357180673 := by
  unfold tailWord_1772043
  simp only [CollatzResearch.WordTrace]
  refine ⟨64631717919198326695040783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43087811946132217796693855 64631717919198326695040783)
  ·
    refine ⟨96947576878797490042561175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64631717919198326695040783 96947576878797490042561175)
    ·
      refine ⟨145421365318196235063841763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96947576878797490042561175 145421365318196235063841763)
      ·
        refine ⟨218132047977294352595762645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145421365318196235063841763 218132047977294352595762645)
        ·
          refine ⟨5112469874467836388963187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 218132047977294352595762645 5112469874467836388963187)
          ·
            refine ⟨7668704811701754583444781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5112469874467836388963187 7668704811701754583444781)
            ·
              refine ⟨2875764304388157968791793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7668704811701754583444781 2875764304388157968791793)
              ·
                refine ⟨2156823228291118476593845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2875764304388157968791793 2156823228291118476593845)
                ·
                  refine ⟨202202177652292357180673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2156823228291118476593845 202202177652292357180673)
                  ·
                    rfl

theorem cell22_1772043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 2, 5].length) (baseStart_1772043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1772043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1772043 prefixEnd_1772043 := by exact prefixLift 1772043
  have htrace : WordTrace (prefixWord ++ tailWord_1772043) baseStart_1772043 baseEnd_1772043 := by
    simpa [prefixWord, tailWord_1772043, baseEnd_1772043] using wordTrace_append hprefix tailTrace_1772043
  have hstable : (prefixWord ++ tailWord_1772043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772043).length < 2 ^ (prefixWord ++ tailWord_1772043).sum := by decide
  have hdescent : baseEnd_1772043 < baseStart_1772043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772060 : List Nat := [2, 2, 3, 1, 2, 3, 3, 1, 5]
def baseStart_1772060 : Nat := 118140960795 + 1772060 * 2 ^ 59
def prefixEnd_1772060 : Nat := 4983230072969 + 3 ^ 40 * 1772060 * 2
def baseEnd_1772060 : Nat := 202204117468098231288989

theorem tailTrace_1772060 : CollatzResearch.WordTrace tailWord_1772060 prefixEnd_1772060 202204117468098231288989 := by
  unfold tailWord_1772060
  simp only [CollatzResearch.WordTrace]
  refine ⟨32316168980068369299204817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43088225306757825732273089 32316168980068369299204817)
  ·
    refine ⟨24237126735051276974403613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32316168980068369299204817 24237126735051276974403613)
    ·
      refine ⟨9088922525644228865401355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24237126735051276974403613 9088922525644228865401355)
      ·
        refine ⟨13633383788466343298102033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9088922525644228865401355 13633383788466343298102033)
        ·
          refine ⟨10225037841349757473576525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13633383788466343298102033 10225037841349757473576525)
          ·
            refine ⟨3834389190506159052591197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10225037841349757473576525 3834389190506159052591197)
            ·
              refine ⟨1437895946439809644721699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3834389190506159052591197 1437895946439809644721699)
              ·
                refine ⟨2156843919659714467082549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1437895946439809644721699 2156843919659714467082549)
                ·
                  refine ⟨202204117468098231288989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2156843919659714467082549 202204117468098231288989)
                  ·
                    rfl

theorem cell22_1772060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 1, 5].length) (baseStart_1772060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1772060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1772060 prefixEnd_1772060 := by exact prefixLift 1772060
  have htrace : WordTrace (prefixWord ++ tailWord_1772060) baseStart_1772060 baseEnd_1772060 := by
    simpa [prefixWord, tailWord_1772060, baseEnd_1772060] using wordTrace_append hprefix tailTrace_1772060
  have hstable : (prefixWord ++ tailWord_1772060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772060).length < 2 ^ (prefixWord ++ tailWord_1772060).sum := by decide
  have hdescent : baseEnd_1772060 < baseStart_1772060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772124 : List Nat := [2, 2, 4, 1, 4, 1, 1, 2, 1, 4]
def baseStart_1772124 : Nat := 118140960795 + 1772124 * 2 ^ 59
def prefixEnd_1772124 : Nat := 4983230072969 + 3 ^ 40 * 1772124 * 2
def baseEnd_1772124 : Nat := 606634260912219860266771

theorem tailTrace_1772124 : CollatzResearch.WordTrace tailWord_1772124 prefixEnd_1772124 606634260912219860266771 := by
  unfold tailWord_1772124
  simp only [CollatzResearch.WordTrace]
  refine ⟨32317336115952438764369713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43089781487936585019159617 32317336115952438764369713)
  ·
    refine ⟨24238002086964329073277285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32317336115952438764369713 24238002086964329073277285)
    ·
      refine ⟨4544625391305811701239491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24238002086964329073277285 4544625391305811701239491)
      ·
        refine ⟨6816938086958717551859237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4544625391305811701239491 6816938086958717551859237)
        ·
          refine ⟨1278175891304759540973607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6816938086958717551859237 1278175891304759540973607)
          ·
            refine ⟨1917263836957139311460411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1278175891304759540973607 1917263836957139311460411)
            ·
              refine ⟨2875895755435708967190617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1917263836957139311460411 2875895755435708967190617)
              ·
                refine ⟨2156921816576781725392963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2875895755435708967190617 2156921816576781725392963)
                ·
                  refine ⟨3235382724865172588089445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2156921816576781725392963 3235382724865172588089445)
                  ·
                    refine ⟨606634260912219860266771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3235382724865172588089445 606634260912219860266771)
                    ·
                      rfl

theorem cell22_1772124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_1772124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1772124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1772124 prefixEnd_1772124 := by exact prefixLift 1772124
  have htrace : WordTrace (prefixWord ++ tailWord_1772124) baseStart_1772124 baseEnd_1772124 := by
    simpa [prefixWord, tailWord_1772124, baseEnd_1772124] using wordTrace_append hprefix tailTrace_1772124
  have hstable : (prefixWord ++ tailWord_1772124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772124).length < 2 ^ (prefixWord ++ tailWord_1772124).sum := by decide
  have hdescent : baseEnd_1772124 < baseStart_1772124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772150 : List Nat := [5, 1, 1, 2, 4, 9]
def baseStart_1772150 : Nat := 118140960795 + 1772150 * 2 ^ 59
def prefixEnd_1772150 : Nat := 4983230072969 + 3 ^ 40 * 1772150 * 2
def baseEnd_1772150 : Nat := 7489421743747709371811

theorem tailTrace_1772150 : CollatzResearch.WordTrace tailWord_1772150 prefixEnd_1772150 7489421743747709371811 := by
  unfold tailWord_1772150
  simp only [CollatzResearch.WordTrace]
  refine ⟨4039726283113167748074119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43090413686540455979457269 4039726283113167748074119)
  ·
    refine ⟨6059589424669751622111179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4039726283113167748074119 6059589424669751622111179)
    ·
      refine ⟨9089384137004627433166769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6059589424669751622111179 9089384137004627433166769)
      ·
        refine ⟨6817038102753470574875077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9089384137004627433166769 6817038102753470574875077)
        ·
          refine ⟨1278194644266275732789077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6817038102753470574875077 1278194644266275732789077)
          ·
            refine ⟨7489421743747709371811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1278194644266275732789077 7489421743747709371811)
            ·
              rfl

theorem cell22_1772150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 9].length) (baseStart_1772150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1772150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1772150 prefixEnd_1772150 := by exact prefixLift 1772150
  have htrace : WordTrace (prefixWord ++ tailWord_1772150) baseStart_1772150 baseEnd_1772150 := by
    simpa [prefixWord, tailWord_1772150, baseEnd_1772150] using wordTrace_append hprefix tailTrace_1772150
  have hstable : (prefixWord ++ tailWord_1772150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772150).length < 2 ^ (prefixWord ++ tailWord_1772150).sum := by decide
  have hdescent : baseEnd_1772150 < baseStart_1772150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772223 : List Nat := [1, 1, 2, 2, 2, 4, 1, 3, 6]
def baseStart_1772223 : Nat := 118140960795 + 1772223 * 2 ^ 59
def prefixEnd_1772223 : Nat := 4983230072969 + 3 ^ 40 * 1772223 * 2
def baseEnd_1772223 : Nat := 202222716878472200680489

theorem tailTrace_1772223 : CollatzResearch.WordTrace tailWord_1772223 prefixEnd_1772223 202222716878472200680489 := by
  unfold tailWord_1772223
  simp only [CollatzResearch.WordTrace]
  refine ⟨64638283058546217436593323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43092188705697478291062215 64638283058546217436593323)
  ·
    refine ⟨96957424587819326154889985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64638283058546217436593323 96957424587819326154889985)
    ·
      refine ⟨72718068440864494616167489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96957424587819326154889985 72718068440864494616167489)
      ·
        refine ⟨54538551330648370962125617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72718068440864494616167489 54538551330648370962125617)
        ·
          refine ⟨40903913497986278221594213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54538551330648370962125617 40903913497986278221594213)
          ·
            refine ⟨7669483780872427166548915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40903913497986278221594213 7669483780872427166548915)
            ·
              refine ⟨11504225671308640749823373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7669483780872427166548915 11504225671308640749823373)
              ·
                refine ⟨4314084626740740281183765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11504225671308640749823373 4314084626740740281183765)
                ·
                  refine ⟨202222716878472200680489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4314084626740740281183765 202222716878472200680489)
                  ·
                    rfl

theorem cell22_1772223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3, 6].length) (baseStart_1772223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1772223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1772223 prefixEnd_1772223 := by exact prefixLift 1772223
  have htrace : WordTrace (prefixWord ++ tailWord_1772223) baseStart_1772223 baseEnd_1772223 := by
    simpa [prefixWord, tailWord_1772223, baseEnd_1772223] using wordTrace_append hprefix tailTrace_1772223
  have hstable : (prefixWord ++ tailWord_1772223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772223).length < 2 ^ (prefixWord ++ tailWord_1772223).sum := by decide
  have hdescent : baseEnd_1772223 < baseStart_1772223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772255 : List Nat := [1, 1, 2, 3, 2, 3, 1, 2, 4, 3]
def baseStart_1772255 : Nat := 118140960795 + 1772255 * 2 ^ 59
def prefixEnd_1772255 : Nat := 4983230072969 + 3 ^ 40 * 1772255 * 2
def baseEnd_1772255 : Nat := 606679104889379185241369

theorem tailTrace_1772255 : CollatzResearch.WordTrace tailWord_1772255 prefixEnd_1772255 606679104889379185241369 := by
  unfold tailWord_1772255
  simp only [CollatzResearch.WordTrace]
  refine ⟨64639450194430286901758219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43092966796286857934505479 64639450194430286901758219)
  ·
    refine ⟨96959175291645430352637329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64639450194430286901758219 96959175291645430352637329)
    ·
      refine ⟨72719381468734072764477997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96959175291645430352637329 72719381468734072764477997)
      ·
        refine ⟨27269768050775277286679249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72719381468734072764477997 27269768050775277286679249)
        ·
          refine ⟨20452326038081457965009437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27269768050775277286679249 20452326038081457965009437)
          ·
            refine ⟨7669622264280546736878539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20452326038081457965009437 7669622264280546736878539)
            ·
              refine ⟨11504433396420820105317809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7669622264280546736878539 11504433396420820105317809)
              ·
                refine ⟨8628325047315615078988357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11504433396420820105317809 8628325047315615078988357)
                ·
                  refine ⟨1617810946371677827310317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8628325047315615078988357 1617810946371677827310317)
                  ·
                    refine ⟨606679104889379185241369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1617810946371677827310317 606679104889379185241369)
                    ·
                      rfl

theorem cell22_1772255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 4, 3].length) (baseStart_1772255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1772255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1772255 prefixEnd_1772255 := by exact prefixLift 1772255
  have htrace : WordTrace (prefixWord ++ tailWord_1772255) baseStart_1772255 baseEnd_1772255 := by
    simpa [prefixWord, tailWord_1772255, baseEnd_1772255] using wordTrace_append hprefix tailTrace_1772255
  have hstable : (prefixWord ++ tailWord_1772255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772255).length < 2 ^ (prefixWord ++ tailWord_1772255).sum := by decide
  have hdescent : baseEnd_1772255 < baseStart_1772255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772257 : List Nat := [1, 2, 3, 1, 4, 1, 3, 3, 4]
def baseStart_1772257 : Nat := 118140960795 + 1772257 * 2 ^ 59
def prefixEnd_1772257 : Nat := 4983230072969 + 3 ^ 40 * 1772257 * 2
def baseEnd_1772257 : Nat := 202226596510083948897121

theorem tailTrace_1772257 : CollatzResearch.WordTrace tailWord_1772257 prefixEnd_1772257 202226596510083948897121 := by
  unfold tailWord_1772257
  simp only [CollatzResearch.WordTrace]
  refine ⟨64639523140423041243331025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43093015426948694162220683 64639523140423041243331025)
  ·
    refine ⟨48479642355317280932498269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64639523140423041243331025 48479642355317280932498269)
    ·
      refine ⟨18179865883243980349686851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48479642355317280932498269 18179865883243980349686851)
      ·
        refine ⟨27269798824865970524530277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18179865883243980349686851 27269798824865970524530277)
        ·
          refine ⟨5113087279662369473349427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27269798824865970524530277 5113087279662369473349427)
          ·
            refine ⟨7669630919493554210024141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5113087279662369473349427 7669630919493554210024141)
            ·
              refine ⟨2876111594810082828759053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7669630919493554210024141 2876111594810082828759053)
              ·
                refine ⟨1078541848053781060784645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2876111594810082828759053 1078541848053781060784645)
                ·
                  refine ⟨202226596510083948897121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1078541848053781060784645 202226596510083948897121)
                  ·
                    rfl

theorem cell22_1772257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 3, 4].length) (baseStart_1772257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1772257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1772257 prefixEnd_1772257 := by exact prefixLift 1772257
  have htrace : WordTrace (prefixWord ++ tailWord_1772257) baseStart_1772257 baseEnd_1772257 := by
    simpa [prefixWord, tailWord_1772257, baseEnd_1772257] using wordTrace_append hprefix tailTrace_1772257
  have hstable : (prefixWord ++ tailWord_1772257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772257).length < 2 ^ (prefixWord ++ tailWord_1772257).sum := by decide
  have hdescent : baseEnd_1772257 < baseStart_1772257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772270 : List Nat := [4, 1, 2, 1, 1, 3, 1, 1, 4, 4]
def baseStart_1772270 : Nat := 118140960795 + 1772270 * 2 ^ 59
def prefixEnd_1772270 : Nat := 4983230072969 + 3 ^ 40 * 1772270 * 2
def baseEnd_1772270 : Nat := 606684239695924146116323

theorem tailTrace_1772270 : CollatzResearch.WordTrace tailWord_1772270 prefixEnd_1772270 606684239695924146116323 := by
  unfold tailWord_1772270
  simp only [CollatzResearch.WordTrace]
  refine ⟨8079999661171993057944283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43093331526250629642369509 8079999661171993057944283)
  ·
    refine ⟨12119999491757989586916425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8079999661171993057944283 12119999491757989586916425)
    ·
      refine ⟨9089999618818492190187319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12119999491757989586916425 9089999618818492190187319)
      ·
        refine ⟨13634999428227738285280979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9089999618818492190187319 13634999428227738285280979)
        ·
          refine ⟨20452499142341607427921469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13634999428227738285280979 20452499142341607427921469)
          ·
            refine ⟨7669687178378102785470551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20452499142341607427921469 7669687178378102785470551)
            ·
              refine ⟨11504530767567154178205827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7669687178378102785470551 11504530767567154178205827)
              ·
                refine ⟨17256796151350731267308741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11504530767567154178205827 17256796151350731267308741)
                ·
                  refine ⟨3235649278378262112620389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17256796151350731267308741 3235649278378262112620389)
                  ·
                    refine ⟨606684239695924146116323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3235649278378262112620389 606684239695924146116323)
                    ·
                      rfl

theorem cell22_1772270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_1772270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1772270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1772270 prefixEnd_1772270 := by exact prefixLift 1772270
  have htrace : WordTrace (prefixWord ++ tailWord_1772270) baseStart_1772270 baseEnd_1772270 := by
    simpa [prefixWord, tailWord_1772270, baseEnd_1772270] using wordTrace_append hprefix tailTrace_1772270
  have hstable : (prefixWord ++ tailWord_1772270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772270).length < 2 ^ (prefixWord ++ tailWord_1772270).sum := by decide
  have hdescent : baseEnd_1772270 < baseStart_1772270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772274 : List Nat := [3, 2, 1, 3, 1, 3, 3, 2, 4]
def baseStart_1772274 : Nat := 118140960795 + 1772274 * 2 ^ 59
def prefixEnd_1772274 : Nat := 4983230072969 + 3 ^ 40 * 1772274 * 2
def baseEnd_1772274 : Nat := 202228536325889823005437

theorem tailTrace_1772274 : CollatzResearch.WordTrace tailWord_1772274 prefixEnd_1772274 202228536325889823005437 := by
  unfold tailWord_1772274
  simp only [CollatzResearch.WordTrace]
  refine ⟨16160035795340363286674969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43093428787574302097799917 16160035795340363286674969)
  ·
    refine ⟨12120026846505272465006227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16160035795340363286674969 12120026846505272465006227)
    ·
      refine ⟨18180040269757908697509341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12120026846505272465006227 18180040269757908697509341)
      ·
        refine ⟨6817515101159215761566003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18180040269757908697509341 6817515101159215761566003)
        ·
          refine ⟨10226272651738823642349005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6817515101159215761566003 10226272651738823642349005)
          ·
            refine ⟨3834852244402058865880877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10226272651738823642349005 3834852244402058865880877)
            ·
              refine ⟨1438069591650772074705329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3834852244402058865880877 1438069591650772074705329)
              ·
                refine ⟨1078552193738079056028997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1438069591650772074705329 1078552193738079056028997)
                ·
                  refine ⟨202228536325889823005437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1078552193738079056028997 202228536325889823005437)
                  ·
                    rfl

theorem cell22_1772274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 2, 4].length) (baseStart_1772274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1772274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1772274 prefixEnd_1772274 := by exact prefixLift 1772274
  have htrace : WordTrace (prefixWord ++ tailWord_1772274) baseStart_1772274 baseEnd_1772274 := by
    simpa [prefixWord, tailWord_1772274, baseEnd_1772274] using wordTrace_append hprefix tailTrace_1772274
  have hstable : (prefixWord ++ tailWord_1772274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772274).length < 2 ^ (prefixWord ++ tailWord_1772274).sum := by decide
  have hdescent : baseEnd_1772274 < baseStart_1772274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772300 : List Nat := [2, 2, 1, 2, 2, 1, 1, 3, 5, 3]
def baseStart_1772300 : Nat := 118140960795 + 1772300 * 2 ^ 59
def prefixEnd_1772300 : Nat := 4983230072969 + 3 ^ 40 * 1772300 * 2
def baseEnd_1772300 : Nat := 606694509309014067866231

theorem tailTrace_1772300 : CollatzResearch.WordTrace tailWord_1772300 prefixEnd_1772300 606694509309014067866231 := by
  unfold tailWord_1772300
  simp only [CollatzResearch.WordTrace]
  refine ⟨32320545739633629793573177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43094060986178173058097569 32320545739633629793573177)
  ·
    refine ⟨24240409304725222345179883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32320545739633629793573177 24240409304725222345179883)
    ·
      refine ⟨36360613957087833517769825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24240409304725222345179883 36360613957087833517769825)
      ·
        refine ⟨27270460467815875138327369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36360613957087833517769825 27270460467815875138327369)
        ·
          refine ⟨20452845350861906353745527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27270460467815875138327369 20452845350861906353745527)
          ·
            refine ⟨30679268026292859530618291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20452845350861906353745527 30679268026292859530618291)
            ·
              refine ⟨46018902039439289295927437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30679268026292859530618291 46018902039439289295927437)
              ·
                refine ⟨17257088264789733485972789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46018902039439289295927437 17257088264789733485972789)
                ·
                  refine ⟨1617852024824037514309949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17257088264789733485972789 1617852024824037514309949)
                  ·
                    refine ⟨606694509309014067866231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1617852024824037514309949 606694509309014067866231)
                    ·
                      rfl

theorem cell22_1772300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 5, 3].length) (baseStart_1772300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1772300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1772300 prefixEnd_1772300 := by exact prefixLift 1772300
  have htrace : WordTrace (prefixWord ++ tailWord_1772300) baseStart_1772300 baseEnd_1772300 := by
    simpa [prefixWord, tailWord_1772300, baseEnd_1772300] using wordTrace_append hprefix tailTrace_1772300
  have hstable : (prefixWord ++ tailWord_1772300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772300).length < 2 ^ (prefixWord ++ tailWord_1772300).sum := by decide
  have hdescent : baseEnd_1772300 < baseStart_1772300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772313 : List Nat := [1, 2, 1, 2, 1, 1, 1, 6, 7]
def baseStart_1772313 : Nat := 118140960795 + 1772313 * 2 ^ 59
def prefixEnd_1772313 : Nat := 4983230072969 + 3 ^ 40 * 1772313 * 2
def baseEnd_1772313 : Nat := 202232986491562122430397

theorem tailTrace_1772313 : CollatzResearch.WordTrace tailWord_1772313 prefixEnd_1772313 202232986491562122430397 := by
  unfold tailWord_1772313
  simp only [CollatzResearch.WordTrace]
  refine ⟨64641565628220162807369593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43094377085480108538246395 64641565628220162807369593)
  ·
    refine ⟨48481174221165122105527195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64641565628220162807369593 48481174221165122105527195)
    ·
      refine ⟨72721761331747683158290793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48481174221165122105527195 72721761331747683158290793)
      ·
        refine ⟨54541320998810762368718095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72721761331747683158290793 54541320998810762368718095)
        ·
          refine ⟨81811981498216143553077143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54541320998810762368718095 81811981498216143553077143)
          ·
            refine ⟨122717972247324215329615715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81811981498216143553077143 122717972247324215329615715)
            ·
              refine ⟨184076958370986322994423573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122717972247324215329615715 184076958370986322994423573)
              ·
                refine ⟨8628607423639983890363605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 184076958370986322994423573 8628607423639983890363605)
                ·
                  refine ⟨202232986491562122430397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8628607423639983890363605 202232986491562122430397)
                  ·
                    rfl

theorem cell22_1772313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 7].length) (baseStart_1772313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1772313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1772313 prefixEnd_1772313 := by exact prefixLift 1772313
  have htrace : WordTrace (prefixWord ++ tailWord_1772313) baseStart_1772313 baseEnd_1772313 := by
    simpa [prefixWord, tailWord_1772313, baseEnd_1772313] using wordTrace_append hprefix tailTrace_1772313
  have hstable : (prefixWord ++ tailWord_1772313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772313).length < 2 ^ (prefixWord ++ tailWord_1772313).sum := by decide
  have hdescent : baseEnd_1772313 < baseStart_1772313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772360 : List Nat := [2, 1, 3, 1, 1, 3, 1, 3, 3, 4]
def baseStart_1772360 : Nat := 118140960795 + 1772360 * 2 ^ 59
def prefixEnd_1772360 : Nat := 4983230072969 + 3 ^ 40 * 1772360 * 2
def baseEnd_1772360 : Nat := 606715048535193911366047

theorem tailTrace_1772360 : CollatzResearch.WordTrace tailWord_1772360 prefixEnd_1772360 606715048535193911366047 := by
  unfold tailWord_1772360
  simp only [CollatzResearch.WordTrace]
  refine ⟨32321639929524944917165267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43095519906033259889553689 32321639929524944917165267)
  ·
    refine ⟨48482459894287417375747901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32321639929524944917165267 48482459894287417375747901)
    ·
      refine ⟨18180922460357781515905463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48482459894287417375747901 18180922460357781515905463)
      ·
        refine ⟨27271383690536672273858195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18180922460357781515905463 27271383690536672273858195)
        ·
          refine ⟨40907075535805008410787293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27271383690536672273858195 40907075535805008410787293)
          ·
            refine ⟨15340153325926878154045235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40907075535805008410787293 15340153325926878154045235)
            ·
              refine ⟨23010229988890317231067853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15340153325926878154045235 23010229988890317231067853)
              ·
                refine ⟨8628836245833868961650445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23010229988890317231067853 8628836245833868961650445)
                ·
                  refine ⟨3235813592187700860618917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8628836245833868961650445 3235813592187700860618917)
                  ·
                    refine ⟨606715048535193911366047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3235813592187700860618917 606715048535193911366047)
                    ·
                      rfl

theorem cell22_1772360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_1772360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1772360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1772360 prefixEnd_1772360 := by exact prefixLift 1772360
  have htrace : WordTrace (prefixWord ++ tailWord_1772360) baseStart_1772360 baseEnd_1772360 := by
    simpa [prefixWord, tailWord_1772360, baseEnd_1772360] using wordTrace_append hprefix tailTrace_1772360
  have hstable : (prefixWord ++ tailWord_1772360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772360).length < 2 ^ (prefixWord ++ tailWord_1772360).sum := by decide
  have hdescent : baseEnd_1772360 < baseStart_1772360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772377 : List Nat := [1, 2, 1, 2, 2, 5, 1, 3, 1, 4]
def baseStart_1772377 : Nat := 118140960795 + 1772377 * 2 ^ 59
def prefixEnd_1772377 : Nat := 4983230072969 + 3 ^ 40 * 1772377 * 2
def baseEnd_1772377 : Nat := 606720867982611533690995

theorem tailTrace_1772377 : CollatzResearch.WordTrace tailWord_1772377 prefixEnd_1772377 606720867982611533690995 := by
  unfold tailWord_1772377
  simp only [CollatzResearch.WordTrace]
  refine ⟨64643899899988301737699385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43095933266658867825132923 64643899899988301737699385)
  ·
    refine ⟨48482924924991226303274539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64643899899988301737699385 48482924924991226303274539)
    ·
      refine ⟨72724387387486839454911809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48482924924991226303274539 72724387387486839454911809)
      ·
        refine ⟨54543290540615129591183857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72724387387486839454911809 54543290540615129591183857)
        ·
          refine ⟨40907467905461347193387893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54543290540615129591183857 40907467905461347193387893)
          ·
            refine ⟨3835075116137001299380115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40907467905461347193387893 3835075116137001299380115)
            ·
              refine ⟨5752612674205501949070173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3835075116137001299380115 5752612674205501949070173)
              ·
                refine ⟨2157229752827063230901315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5752612674205501949070173 2157229752827063230901315)
                ·
                  refine ⟨3235844629240594846351973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2157229752827063230901315 3235844629240594846351973)
                  ·
                    refine ⟨606720867982611533690995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3235844629240594846351973 606720867982611533690995)
                    ·
                      rfl

theorem cell22_1772377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 3, 1, 4].length) (baseStart_1772377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1772377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1772377 prefixEnd_1772377 := by exact prefixLift 1772377
  have htrace : WordTrace (prefixWord ++ tailWord_1772377) baseStart_1772377 baseEnd_1772377 := by
    simpa [prefixWord, tailWord_1772377, baseEnd_1772377] using wordTrace_append hprefix tailTrace_1772377
  have hstable : (prefixWord ++ tailWord_1772377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772377).length < 2 ^ (prefixWord ++ tailWord_1772377).sum := by decide
  have hdescent : baseEnd_1772377 < baseStart_1772377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772392 : List Nat := [2, 1, 4, 2, 1, 3, 2, 1, 6]
def baseStart_1772392 : Nat := 118140960795 + 1772392 * 2 ^ 59
def prefixEnd_1772392 : Nat := 4983230072969 + 3 ^ 40 * 1772392 * 2
def baseEnd_1772392 : Nat := 202242000929718831521983

theorem tailTrace_1772392 : CollatzResearch.WordTrace tailWord_1772392 prefixEnd_1772392 202242000929718831521983 := by
  unfold tailWord_1772392
  simp only [CollatzResearch.WordTrace]
  refine ⟨32322223497466979649747715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43096297996622639532996953 32322223497466979649747715)
  ·
    refine ⟨48483335246200469474621573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32322223497466979649747715 48483335246200469474621573)
    ·
      refine ⟨9090625358662588026491545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48483335246200469474621573 9090625358662588026491545)
      ·
        refine ⟨6817969018996941019868659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9090625358662588026491545 6817969018996941019868659)
        ·
          refine ⟨10226953528495411529802989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6817969018996941019868659 10226953528495411529802989)
          ·
            refine ⟨3835107573185779323676121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10226953528495411529802989 3835107573185779323676121)
            ·
              refine ⟨2876330679889334492757091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3835107573185779323676121 2876330679889334492757091)
              ·
                refine ⟨4314496019834001739135637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2876330679889334492757091 4314496019834001739135637)
                ·
                  refine ⟨202242000929718831521983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4314496019834001739135637 202242000929718831521983)
                  ·
                    rfl

theorem cell22_1772392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 1, 6].length) (baseStart_1772392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1772392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1772392 prefixEnd_1772392 := by exact prefixLift 1772392
  have htrace : WordTrace (prefixWord ++ tailWord_1772392) baseStart_1772392 baseEnd_1772392 := by
    simpa [prefixWord, tailWord_1772392, baseEnd_1772392] using wordTrace_append hprefix tailTrace_1772392
  have hstable : (prefixWord ++ tailWord_1772392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772392).length < 2 ^ (prefixWord ++ tailWord_1772392).sum := by decide
  have hdescent : baseEnd_1772392 < baseStart_1772392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772407 : List Nat := [1, 1, 3, 1, 1, 2, 1, 7, 2, 3]
def baseStart_1772407 : Nat := 118140960795 + 1772407 * 2 ^ 59
def prefixEnd_1772407 : Nat := 4983230072969 + 3 ^ 40 * 1772407 * 2
def baseEnd_1772407 : Nat := 606731137595701455440903

theorem tailTrace_1772407 : CollatzResearch.WordTrace tailWord_1772407 prefixEnd_1772407 606731137595701455440903 := by
  unfold tailWord_1772407
  simp only [CollatzResearch.WordTrace]
  refine ⟨64644994089879616861291475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43096662726586411240860983 64644994089879616861291475)
  ·
    refine ⟨96967491134819425291937213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64644994089879616861291475 96967491134819425291937213)
    ·
      refine ⟨36362809175557284484476455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96967491134819425291937213 36362809175557284484476455)
      ·
        refine ⟨54544213763335926726714683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36362809175557284484476455 54544213763335926726714683)
        ·
          refine ⟨81816320645003890090072025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54544213763335926726714683 81816320645003890090072025)
          ·
            refine ⟨61362240483752917567554019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81816320645003890090072025 61362240483752917567554019)
            ·
              refine ⟨92043360725629376351331029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61362240483752917567554019 92043360725629376351331029)
              ·
                refine ⟨2157266267006938508234321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 92043360725629376351331029 2157266267006938508234321)
                ·
                  refine ⟨1617949700255203881175741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2157266267006938508234321 1617949700255203881175741)
                  ·
                    refine ⟨606731137595701455440903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1617949700255203881175741 606731137595701455440903)
                    ·
                      rfl

theorem cell22_1772407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 7, 2, 3].length) (baseStart_1772407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1772407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1772407 prefixEnd_1772407 := by exact prefixLift 1772407
  have htrace : WordTrace (prefixWord ++ tailWord_1772407) baseStart_1772407 baseEnd_1772407 := by
    simpa [prefixWord, tailWord_1772407, baseEnd_1772407] using wordTrace_append hprefix tailTrace_1772407
  have hstable : (prefixWord ++ tailWord_1772407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772407).length < 2 ^ (prefixWord ++ tailWord_1772407).sum := by decide
  have hdescent : baseEnd_1772407 < baseStart_1772407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772426 : List Nat := [3, 1, 2, 4, 1, 3, 1, 3, 4]
def baseStart_1772426 : Nat := 118140960795 + 1772426 * 2 ^ 59
def prefixEnd_1772426 : Nat := 4983230072969 + 3 ^ 40 * 1772426 * 2
def baseEnd_1772426 : Nat := 202245880561330579738615

theorem tailTrace_1772426 : CollatzResearch.WordTrace tailWord_1772426 prefixEnd_1772426 202245880561330579738615 := by
  unfold tailWord_1772426
  simp only [CollatzResearch.WordTrace]
  refine ⟨16161421769202695776558283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43097124717873855404155421 16161421769202695776558283)
  ·
    refine ⟨24242132653804043664837425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16161421769202695776558283 24242132653804043664837425)
    ·
      refine ⟨18181599490353032748628069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24242132653804043664837425 18181599490353032748628069)
      ·
        refine ⟨3409049904441193640367763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18181599490353032748628069 3409049904441193640367763)
        ·
          refine ⟨5113574856661790460551645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3409049904441193640367763 5113574856661790460551645)
          ·
            refine ⟨1917590571248171422706867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5113574856661790460551645 1917590571248171422706867)
            ·
              refine ⟨2876385856872257134060301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1917590571248171422706867 2876385856872257134060301)
              ·
                refine ⟨1078644696327096425272613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2876385856872257134060301 1078644696327096425272613)
                ·
                  refine ⟨202245880561330579738615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1078644696327096425272613 202245880561330579738615)
                  ·
                    rfl

theorem cell22_1772426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 3, 4].length) (baseStart_1772426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1772426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1772426 prefixEnd_1772426 := by exact prefixLift 1772426
  have htrace : WordTrace (prefixWord ++ tailWord_1772426) baseStart_1772426 baseEnd_1772426 := by
    simpa [prefixWord, tailWord_1772426, baseEnd_1772426] using wordTrace_append hprefix tailTrace_1772426
  have hstable : (prefixWord ++ tailWord_1772426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772426).length < 2 ^ (prefixWord ++ tailWord_1772426).sum := by decide
  have hdescent : baseEnd_1772426 < baseStart_1772426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772514 : List Nat := [3, 3, 3, 1, 1, 1, 1, 1, 1, 7]
def baseStart_1772514 : Nat := 118140960795 + 1772514 * 2 ^ 59
def prefixEnd_1772514 : Nat := 4983230072969 + 3 ^ 40 * 1772514 * 2
def baseEnd_1772514 : Nat := 606767765882388843015575

theorem tailTrace_1772514 : CollatzResearch.WordTrace tailWord_1772514 prefixEnd_1772514 606767765882388843015575 := by
  unfold tailWord_1772514
  simp only [CollatzResearch.WordTrace]
  refine ⟨16162224175122993533859149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43099264466994649423624397 16162224175122993533859149)
  ·
    refine ⟨6060834065671122575197181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16162224175122993533859149 6060834065671122575197181)
    ·
      refine ⟨2272812774626670965698943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6060834065671122575197181 2272812774626670965698943)
      ·
        refine ⟨3409219161940006448548415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2272812774626670965698943 3409219161940006448548415)
        ·
          refine ⟨5113828742910009672822623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3409219161940006448548415 5113828742910009672822623)
          ·
            refine ⟨7670743114365014509233935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5113828742910009672822623 7670743114365014509233935)
            ·
              refine ⟨11506114671547521763850903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7670743114365014509233935 11506114671547521763850903)
              ·
                refine ⟨17259172007321282645776355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11506114671547521763850903 17259172007321282645776355)
                ·
                  refine ⟨25888758010981923968664533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17259172007321282645776355 25888758010981923968664533)
                  ·
                    refine ⟨606767765882388843015575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25888758010981923968664533 606767765882388843015575)
                    ·
                      rfl

theorem cell22_1772514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_1772514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1772514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1772514 prefixEnd_1772514 := by exact prefixLift 1772514
  have htrace : WordTrace (prefixWord ++ tailWord_1772514) baseStart_1772514 baseEnd_1772514 := by
    simpa [prefixWord, tailWord_1772514, baseEnd_1772514] using wordTrace_append hprefix tailTrace_1772514
  have hstable : (prefixWord ++ tailWord_1772514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772514).length < 2 ^ (prefixWord ++ tailWord_1772514).sum := by decide
  have hdescent : baseEnd_1772514 < baseStart_1772514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772527 : List Nat := [1, 1, 2, 1, 4, 4, 1, 2, 6]
def baseStart_1772527 : Nat := 118140960795 + 1772527 * 2 ^ 59
def prefixEnd_1772527 : Nat := 4983230072969 + 3 ^ 40 * 1772527 * 2
def baseEnd_1772527 : Nat := 202257405349353714146845

theorem tailTrace_1772527 : CollatzResearch.WordTrace tailWord_1772527 prefixEnd_1772527 202257405349353714146845 := by
  unfold tailWord_1772527
  simp only [CollatzResearch.WordTrace]
  refine ⟨64649370849444877355659835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43099580566296584903773223 64649370849444877355659835)
  ·
    refine ⟨96974056274167316033489753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64649370849444877355659835 96974056274167316033489753)
    ·
      refine ⟨72730542205625487025117315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96974056274167316033489753 72730542205625487025117315)
      ·
        refine ⟨109095813308438230537675973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72730542205625487025117315 109095813308438230537675973)
        ·
          refine ⟨20455464995332168225814245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109095813308438230537675973 20455464995332168225814245)
          ·
            refine ⟨3835399686624781542340171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20455464995332168225814245 3835399686624781542340171)
            ·
              refine ⟨5753099529937172313510257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3835399686624781542340171 5753099529937172313510257)
              ·
                refine ⟨4314824647452879235132693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5753099529937172313510257 4314824647452879235132693)
                ·
                  refine ⟨202257405349353714146845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4314824647452879235132693 202257405349353714146845)
                  ·
                    rfl

theorem cell22_1772527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 2, 6].length) (baseStart_1772527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1772527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1772527 prefixEnd_1772527 := by exact prefixLift 1772527
  have htrace : WordTrace (prefixWord ++ tailWord_1772527) baseStart_1772527 baseEnd_1772527 := by
    simpa [prefixWord, tailWord_1772527, baseEnd_1772527] using wordTrace_append hprefix tailTrace_1772527
  have hstable : (prefixWord ++ tailWord_1772527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772527).length < 2 ^ (prefixWord ++ tailWord_1772527).sum := by decide
  have hdescent : baseEnd_1772527 < baseStart_1772527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772632 : List Nat := [2, 1, 2, 2, 1, 3, 2, 1, 1, 7]
def baseStart_1772632 : Nat := 118140960795 + 1772632 * 2 ^ 59
def prefixEnd_1772632 : Nat := 4983230072969 + 3 ^ 40 * 1772632 * 2
def baseEnd_1772632 : Nat := 606808159693875868565213

theorem tailTrace_1772632 : CollatzResearch.WordTrace tailWord_1772632 prefixEnd_1772632 606808159693875868565213 := by
  unfold tailWord_1772632
  simp only [CollatzResearch.WordTrace]
  refine ⟨32326600257032240144116075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43102133676042986858821433 32326600257032240144116075)
  ·
    refine ⟨48489900385548360216174113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32326600257032240144116075 48489900385548360216174113)
    ·
      refine ⟨36367425289161270162130585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48489900385548360216174113 36367425289161270162130585)
      ·
        refine ⟨27275568966870952621597939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36367425289161270162130585 27275568966870952621597939)
        ·
          refine ⟨40913353450306428932396909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27275568966870952621597939 40913353450306428932396909)
          ·
            refine ⟨15342507543864910849648841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40913353450306428932396909 15342507543864910849648841)
            ·
              refine ⟨11506880657898683137236631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15342507543864910849648841 11506880657898683137236631)
              ·
                refine ⟨17260320986848024705854947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11506880657898683137236631 17260320986848024705854947)
                ·
                  refine ⟨25890481480272037058782421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17260320986848024705854947 25890481480272037058782421)
                  ·
                    refine ⟨606808159693875868565213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25890481480272037058782421 606808159693875868565213)
                    ·
                      rfl

theorem cell22_1772632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 1, 7].length) (baseStart_1772632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1772632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1772632 prefixEnd_1772632 := by exact prefixLift 1772632
  have htrace : WordTrace (prefixWord ++ tailWord_1772632) baseStart_1772632 baseEnd_1772632 := by
    simpa [prefixWord, tailWord_1772632, baseEnd_1772632] using wordTrace_append hprefix tailTrace_1772632
  have hstable : (prefixWord ++ tailWord_1772632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772632).length < 2 ^ (prefixWord ++ tailWord_1772632).sum := by decide
  have hdescent : baseEnd_1772632 < baseStart_1772632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772664 : List Nat := [2, 1, 2, 1, 1, 1, 4, 5, 1, 4]
def baseStart_1772664 : Nat := 118140960795 + 1772664 * 2 ^ 59
def prefixEnd_1772664 : Nat := 4983230072969 + 3 ^ 40 * 1772664 * 2
def baseEnd_1772664 : Nat := 606819113947838451765115

theorem tailTrace_1772664 : CollatzResearch.WordTrace tailWord_1772664 prefixEnd_1772664 606819113947838451765115 := by
  unfold tailWord_1772664
  simp only [CollatzResearch.WordTrace]
  refine ⟨32327183824974274876698523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43102911766632366502264697 32327183824974274876698523)
  ·
    refine ⟨48490775737461412315047785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32327183824974274876698523 48490775737461412315047785)
    ·
      refine ⟨36368081803096059236285839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48490775737461412315047785 36368081803096059236285839)
      ·
        refine ⟨54552122704644088854428759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36368081803096059236285839 54552122704644088854428759)
        ·
          refine ⟨81828184056966133281643139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54552122704644088854428759 81828184056966133281643139)
          ·
            refine ⟨122742276085449199922464709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81828184056966133281643139 122742276085449199922464709)
            ·
              refine ⟨23014176766021724985462133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122742276085449199922464709 23014176766021724985462133)
              ·
                refine ⟨2157579071814536717387075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23014176766021724985462133 2157579071814536717387075)
                ·
                  refine ⟨3236368607721805076080613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2157579071814536717387075 3236368607721805076080613)
                  ·
                    refine ⟨606819113947838451765115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3236368607721805076080613 606819113947838451765115)
                    ·
                      rfl

theorem cell22_1772664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 5, 1, 4].length) (baseStart_1772664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1772664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1772664 prefixEnd_1772664 := by exact prefixLift 1772664
  have htrace : WordTrace (prefixWord ++ tailWord_1772664) baseStart_1772664 baseEnd_1772664 := by
    simpa [prefixWord, tailWord_1772664, baseEnd_1772664] using wordTrace_append hprefix tailTrace_1772664
  have hstable : (prefixWord ++ tailWord_1772664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772664).length < 2 ^ (prefixWord ++ tailWord_1772664).sum := by decide
  have hdescent : baseEnd_1772664 < baseStart_1772664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772707 : List Nat := [1, 1, 1, 4, 1, 1, 1, 12]
def baseStart_1772707 : Nat := 118140960795 + 1772707 * 2 ^ 59
def prefixEnd_1772707 : Nat := 4983230072969 + 3 ^ 40 * 1772707 * 2
def baseEnd_1772707 : Nat := 67425981525177852548887

theorem tailTrace_1772707 : CollatzResearch.WordTrace tailWord_1772707 prefixEnd_1772707 67425981525177852548887 := by
  unfold tailWord_1772707
  simp only [CollatzResearch.WordTrace]
  refine ⟨64655935988792768097212375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43103957325861845398141583 64655935988792768097212375)
  ·
    refine ⟨96983903983189152145818563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64655935988792768097212375 96983903983189152145818563)
    ·
      refine ⟨145475855974783728218727845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96983903983189152145818563 145475855974783728218727845)
      ·
        refine ⟨27276722995271949041011471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145475855974783728218727845 27276722995271949041011471)
        ·
          refine ⟨40915084492907923561517207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27276722995271949041011471 40915084492907923561517207)
          ·
            refine ⟨61372626739361885342275811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40915084492907923561517207 61372626739361885342275811)
            ·
              refine ⟨92058940109042828013413717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61372626739361885342275811 92058940109042828013413717)
              ·
                refine ⟨67425981525177852548887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 92058940109042828013413717 67425981525177852548887)
                ·
                  rfl

theorem cell22_1772707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 12].length) (baseStart_1772707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1772707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1772707 prefixEnd_1772707 := by exact prefixLift 1772707
  have htrace : WordTrace (prefixWord ++ tailWord_1772707) baseStart_1772707 baseEnd_1772707 := by
    simpa [prefixWord, tailWord_1772707, baseEnd_1772707] using wordTrace_append hprefix tailTrace_1772707
  have hstable : (prefixWord ++ tailWord_1772707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772707).length < 2 ^ (prefixWord ++ tailWord_1772707).sum := by decide
  have hdescent : baseEnd_1772707 < baseStart_1772707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772709 : List Nat := [1, 3, 1, 2, 1, 5, 1, 1, 1, 6]
def baseStart_1772709 : Nat := 118140960795 + 1772709 * 2 ^ 59
def prefixEnd_1772709 : Nat := 4983230072969 + 3 ^ 40 * 1772709 * 2
def baseEnd_1772709 : Nat := 606834518367473334389977

theorem tailTrace_1772709 : CollatzResearch.WordTrace tailWord_1772709 prefixEnd_1772709 606834518367473334389977 := by
  unfold tailWord_1772709
  simp only [CollatzResearch.WordTrace]
  refine ⟨64656008934785522438785181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43104005956523681625856787 64656008934785522438785181)
  ·
    refine ⟨24246003350544570914544443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64656008934785522438785181 24246003350544570914544443)
    ·
      refine ⟨36369005025816856371816665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24246003350544570914544443 36369005025816856371816665)
      ·
        refine ⟨27276753769362642278862499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36369005025816856371816665 27276753769362642278862499)
        ·
          refine ⟨40915130654043963418293749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27276753769362642278862499 40915130654043963418293749)
          ·
            refine ⟨3835793498816621570465039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40915130654043963418293749 3835793498816621570465039)
            ·
              refine ⟨5753690248224932355697559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3835793498816621570465039 5753690248224932355697559)
              ·
                refine ⟨8630535372337398533546339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5753690248224932355697559 8630535372337398533546339)
                ·
                  refine ⟨12945803058506097800319509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8630535372337398533546339 12945803058506097800319509)
                  ·
                    refine ⟨606834518367473334389977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12945803058506097800319509 606834518367473334389977)
                    ·
                      rfl

theorem cell22_1772709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 6].length) (baseStart_1772709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1772709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1772709 prefixEnd_1772709 := by exact prefixLift 1772709
  have htrace : WordTrace (prefixWord ++ tailWord_1772709) baseStart_1772709 baseEnd_1772709 := by
    simpa [prefixWord, tailWord_1772709, baseEnd_1772709] using wordTrace_append hprefix tailTrace_1772709
  have hstable : (prefixWord ++ tailWord_1772709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772709).length < 2 ^ (prefixWord ++ tailWord_1772709).sum := by decide
  have hdescent : baseEnd_1772709 < baseStart_1772709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772711 : List Nat := [1, 1, 6, 2, 1, 1, 2, 2, 1, 5]
def baseStart_1772711 : Nat := 118140960795 + 1772711 * 2 ^ 59
def prefixEnd_1772711 : Nat := 4983230072969 + 3 ^ 40 * 1772711 * 2
def baseEnd_1772711 : Nat := 606835203008345995839971

theorem tailTrace_1772711 : CollatzResearch.WordTrace tailWord_1772711 prefixEnd_1772711 606835203008345995839971 := by
  unfold tailWord_1772711
  simp only [CollatzResearch.WordTrace]
  refine ⟨64656081880778276780357987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43104054587185517853571991 64656081880778276780357987)
  ·
    refine ⟨96984122821167415170536981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64656081880778276780357987 96984122821167415170536981)
    ·
      refine ⟨4546130757242222586118921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 96984122821167415170536981 4546130757242222586118921)
      ·
        refine ⟨3409598067931666939589191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4546130757242222586118921 3409598067931666939589191)
        ·
          refine ⟨5114397101897500409383787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3409598067931666939589191 5114397101897500409383787)
          ·
            refine ⟨7671595652846250614075681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5114397101897500409383787 7671595652846250614075681)
            ·
              refine ⟨5753696739634687960556761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7671595652846250614075681 5753696739634687960556761)
              ·
                refine ⟨4315272554726015970417571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5753696739634687960556761 4315272554726015970417571)
                ·
                  refine ⟨6472908832089023955626357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4315272554726015970417571 6472908832089023955626357)
                  ·
                    refine ⟨606835203008345995839971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6472908832089023955626357 606835203008345995839971)
                    ·
                      rfl

theorem cell22_1772711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_1772711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1772711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1772711 prefixEnd_1772711 := by exact prefixLift 1772711
  have htrace : WordTrace (prefixWord ++ tailWord_1772711) baseStart_1772711 baseEnd_1772711 := by
    simpa [prefixWord, tailWord_1772711, baseEnd_1772711] using wordTrace_append hprefix tailTrace_1772711
  have hstable : (prefixWord ++ tailWord_1772711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772711).length < 2 ^ (prefixWord ++ tailWord_1772711).sum := by decide
  have hdescent : baseEnd_1772711 < baseStart_1772711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772758 : List Nat := [5, 2, 1, 2, 2, 1, 1, 8]
def baseStart_1772758 : Nat := 118140960795 + 1772758 * 2 ^ 59
def prefixEnd_1772758 : Nat := 4983230072969 + 3 ^ 40 * 1772758 * 2
def baseEnd_1772758 : Nat := 67427921340983726657203

theorem tailTrace_1772758 : CollatzResearch.WordTrace tailWord_1772758 prefixEnd_1772758 67427921340983726657203 := by
  unfold tailWord_1772758
  simp only [CollatzResearch.WordTrace]
  refine ⟨4041112256975500237957433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43105197407738669204879285 4041112256975500237957433)
  ·
    refine ⟨3030834192731625178468075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4041112256975500237957433 3030834192731625178468075)
    ·
      refine ⟨4546251289097437767702113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3030834192731625178468075 4546251289097437767702113)
      ·
        refine ⟨3409688466823078325776585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4546251289097437767702113 3409688466823078325776585)
        ·
          refine ⟨2557266350117308744332439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3409688466823078325776585 2557266350117308744332439)
          ·
            refine ⟨3835899525175963116498659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2557266350117308744332439 3835899525175963116498659)
            ·
              refine ⟨5753849287763944674747989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3835899525175963116498659 5753849287763944674747989)
              ·
                refine ⟨67427921340983726657203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5753849287763944674747989 67427921340983726657203)
                ·
                  rfl

theorem cell22_1772758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 8].length) (baseStart_1772758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1772758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1772758 prefixEnd_1772758 := by exact prefixLift 1772758
  have htrace : WordTrace (prefixWord ++ tailWord_1772758) baseStart_1772758 baseEnd_1772758 := by
    simpa [prefixWord, tailWord_1772758, baseEnd_1772758] using wordTrace_append hprefix tailTrace_1772758
  have hstable : (prefixWord ++ tailWord_1772758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772758).length < 2 ^ (prefixWord ++ tailWord_1772758).sum := by decide
  have hdescent : baseEnd_1772758 < baseStart_1772758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772769 : List Nat := [1, 2, 3, 1, 3, 2, 1, 2, 7]
def baseStart_1772769 : Nat := 118140960795 + 1772769 * 2 ^ 59
def prefixEnd_1772769 : Nat := 4983230072969 + 3 ^ 40 * 1772769 * 2
def baseEnd_1772769 : Nat := 202285019197884392629931

theorem tailTrace_1772769 : CollatzResearch.WordTrace tailWord_1772769 prefixEnd_1772769 202285019197884392629931 := by
  unfold tailWord_1772769
  simp only [CollatzResearch.WordTrace]
  refine ⟨64658197314568152685969361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43105464876378768457312907 64658197314568152685969361)
  ·
    refine ⟨48493647985926114514477021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64658197314568152685969361 48493647985926114514477021)
    ·
      refine ⟨18185117994722292942928883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48493647985926114514477021 18185117994722292942928883)
      ·
        refine ⟨27277676992083439414393325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18185117994722292942928883 27277676992083439414393325)
        ·
          refine ⟨10229128872031289780397497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27277676992083439414393325 10229128872031289780397497)
          ·
            refine ⟨7671846654023467335298123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10229128872031289780397497 7671846654023467335298123)
            ·
              refine ⟨11507769981035201002947185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7671846654023467335298123 11507769981035201002947185)
              ·
                refine ⟨8630827485776400752210389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11507769981035201002947185 8630827485776400752210389)
                ·
                  refine ⟨202285019197884392629931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8630827485776400752210389 202285019197884392629931)
                  ·
                    rfl

theorem cell22_1772769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 7].length) (baseStart_1772769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1772769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1772769 prefixEnd_1772769 := by exact prefixLift 1772769
  have htrace : WordTrace (prefixWord ++ tailWord_1772769) baseStart_1772769 baseEnd_1772769 := by
    simpa [prefixWord, tailWord_1772769, baseEnd_1772769] using wordTrace_append hprefix tailTrace_1772769
  have hstable : (prefixWord ++ tailWord_1772769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772769).length < 2 ^ (prefixWord ++ tailWord_1772769).sum := by decide
  have hdescent : baseEnd_1772769 < baseStart_1772769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772803 : List Nat := [1, 1, 1, 3, 2, 6, 2, 1, 5]
def baseStart_1772803 : Nat := 118140960795 + 1772803 * 2 ^ 59
def prefixEnd_1772803 : Nat := 4983230072969 + 3 ^ 40 * 1772803 * 2
def baseEnd_1772803 : Nat := 202288898829496140846563

theorem tailTrace_1772803 : CollatzResearch.WordTrace tailWord_1772803 prefixEnd_1772803 202288898829496140846563 := by
  unfold tailWord_1772803
  simp only [CollatzResearch.WordTrace]
  refine ⟨64659437396444976492707063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43106291597629984328471375 64659437396444976492707063)
  ·
    refine ⟨96989156094667464739060595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64659437396444976492707063 96989156094667464739060595)
    ·
      refine ⟨145483734142001197108590893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96989156094667464739060595 145483734142001197108590893)
      ·
        refine ⟨54556400303250448915721585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145483734142001197108590893 54556400303250448915721585)
        ·
          refine ⟨40917300227437836686791189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54556400303250448915721585 40917300227437836686791189)
          ·
            refine ⟨1917998448161148594693337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 40917300227437836686791189 1917998448161148594693337)
            ·
              refine ⟨1438498836120861446020003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1917998448161148594693337 1438498836120861446020003)
              ·
                refine ⟨2157748254181292169030005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1438498836120861446020003 2157748254181292169030005)
                ·
                  refine ⟨202288898829496140846563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2157748254181292169030005 202288898829496140846563)
                  ·
                    rfl

theorem cell22_1772803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 1, 5].length) (baseStart_1772803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1772803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1772803 prefixEnd_1772803 := by exact prefixLift 1772803
  have htrace : WordTrace (prefixWord ++ tailWord_1772803) baseStart_1772803 baseEnd_1772803 := by
    simpa [prefixWord, tailWord_1772803, baseEnd_1772803] using wordTrace_append hprefix tailTrace_1772803
  have hstable : (prefixWord ++ tailWord_1772803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772803).length < 2 ^ (prefixWord ++ tailWord_1772803).sum := by decide
  have hdescent : baseEnd_1772803 < baseStart_1772803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772844 : List Nat := [2, 2, 1, 1, 1, 3, 1, 2, 3, 6]
def baseStart_1772844 : Nat := 118140960795 + 1772844 * 2 ^ 59
def prefixEnd_1772844 : Nat := 4983230072969 + 3 ^ 40 * 1772844 * 2
def baseEnd_1772844 : Nat := 606880731626377982264563

theorem tailTrace_1772844 : CollatzResearch.WordTrace tailWord_1772844 prefixEnd_1772844 606880731626377982264563 := by
  unfold tailWord_1772844
  simp only [CollatzResearch.WordTrace]
  refine ⟨32330466394648220247474793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43107288526197626996633057 32330466394648220247474793)
  ·
    refine ⟨24247849795986165185606095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32330466394648220247474793 24247849795986165185606095)
    ·
      refine ⟨36371774693979247778409143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24247849795986165185606095 36371774693979247778409143)
      ·
        refine ⟨54557662040968871667613715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36371774693979247778409143 54557662040968871667613715)
        ·
          refine ⟨81836493061453307501420573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54557662040968871667613715 81836493061453307501420573)
          ·
            refine ⟨30688684898044990313032715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81836493061453307501420573 30688684898044990313032715)
            ·
              refine ⟨46033027347067485469549073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30688684898044990313032715 46033027347067485469549073)
              ·
                refine ⟨34524770510300614102161805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46033027347067485469549073 34524770510300614102161805)
                ·
                  refine ⟨12946788941362730288310677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34524770510300614102161805 12946788941362730288310677)
                  ·
                    refine ⟨606880731626377982264563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12946788941362730288310677 606880731626377982264563)
                    ·
                      rfl

theorem cell22_1772844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 6].length) (baseStart_1772844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1772844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1772844 prefixEnd_1772844 := by exact prefixLift 1772844
  have htrace : WordTrace (prefixWord ++ tailWord_1772844) baseStart_1772844 baseEnd_1772844 := by
    simpa [prefixWord, tailWord_1772844, baseEnd_1772844] using wordTrace_append hprefix tailTrace_1772844
  have hstable : (prefixWord ++ tailWord_1772844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772844).length < 2 ^ (prefixWord ++ tailWord_1772844).sum := by decide
  have hdescent : baseEnd_1772844 < baseStart_1772844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772863 : List Nat := [1, 1, 2, 2, 4, 2, 2, 3, 2, 3]
def baseStart_1772863 : Nat := 118140960795 + 1772863 * 2 ^ 59
def prefixEnd_1772863 : Nat := 4983230072969 + 3 ^ 40 * 1772863 * 2
def baseEnd_1772863 : Nat := 606887235714668266039505

theorem tailTrace_1772863 : CollatzResearch.WordTrace tailWord_1772863 prefixEnd_1772863 606887235714668266039505 := by
  unfold tailWord_1772863
  simp only [CollatzResearch.WordTrace]
  refine ⟨64661625776227606739891243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43107750517485071159927495 64661625776227606739891243)
  ·
    refine ⟨96992438664341410109836865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64661625776227606739891243 96992438664341410109836865)
    ·
      refine ⟨72744328998256057582377649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96992438664341410109836865 72744328998256057582377649)
      ·
        refine ⟨54558246748692043186783237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72744328998256057582377649 54558246748692043186783237)
        ·
          refine ⟨10229671265379758097521857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54558246748692043186783237 10229671265379758097521857)
          ·
            refine ⟨7672253449034818573141393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10229671265379758097521857 7672253449034818573141393)
            ·
              refine ⟨5754190086776113929856045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7672253449034818573141393 5754190086776113929856045)
              ·
                refine ⟨2157821282541042723696017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5754190086776113929856045 2157821282541042723696017)
                ·
                  refine ⟨1618365961905782042772013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2157821282541042723696017 1618365961905782042772013)
                  ·
                    refine ⟨606887235714668266039505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1618365961905782042772013 606887235714668266039505)
                    ·
                      rfl

theorem cell22_1772863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 3, 2, 3].length) (baseStart_1772863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1772863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1772863 prefixEnd_1772863 := by exact prefixLift 1772863
  have htrace : WordTrace (prefixWord ++ tailWord_1772863) baseStart_1772863 baseEnd_1772863 := by
    simpa [prefixWord, tailWord_1772863, baseEnd_1772863] using wordTrace_append hprefix tailTrace_1772863
  have hstable : (prefixWord ++ tailWord_1772863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772863).length < 2 ^ (prefixWord ++ tailWord_1772863).sum := by decide
  have hdescent : baseEnd_1772863 < baseStart_1772863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772908 : List Nat := [2, 2, 1, 1, 5, 1, 1, 3, 3, 3]
def baseStart_1772908 : Nat := 118140960795 + 1772908 * 2 ^ 59
def prefixEnd_1772908 : Nat := 4983230072969 + 3 ^ 40 * 1772908 * 2
def baseEnd_1772908 : Nat := 606902640134303148664367

theorem tailTrace_1772908 : CollatzResearch.WordTrace tailWord_1772908 prefixEnd_1772908 606902640134303148664367 := by
  unfold tailWord_1772908
  simp only [CollatzResearch.WordTrace]
  refine ⟨32331633530532289712639689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43108844707376386283519585 32331633530532289712639689)
  ·
    refine ⟨24248725147899217284479767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32331633530532289712639689 24248725147899217284479767)
    ·
      refine ⟨36373087721848825926719651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24248725147899217284479767 36373087721848825926719651)
      ·
        refine ⟨54559631582773238890079477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36373087721848825926719651 54559631582773238890079477)
        ·
          refine ⟨5114965460884991145944951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54559631582773238890079477 5114965460884991145944951)
          ·
            refine ⟨7672448191327486718917427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5114965460884991145944951 7672448191327486718917427)
            ·
              refine ⟨11508672286991230078376141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7672448191327486718917427 11508672286991230078376141)
              ·
                refine ⟨4315752107621711279391053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11508672286991230078376141 4315752107621711279391053)
                ·
                  refine ⟨1618407040358141729771645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4315752107621711279391053 1618407040358141729771645)
                  ·
                    refine ⟨606902640134303148664367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1618407040358141729771645 606902640134303148664367)
                    ·
                      rfl

theorem cell22_1772908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 3].length) (baseStart_1772908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1772908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1772908 prefixEnd_1772908 := by exact prefixLift 1772908
  have htrace : WordTrace (prefixWord ++ tailWord_1772908) baseStart_1772908 baseEnd_1772908 := by
    simpa [prefixWord, tailWord_1772908, baseEnd_1772908] using wordTrace_append hprefix tailTrace_1772908
  have hstable : (prefixWord ++ tailWord_1772908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772908).length < 2 ^ (prefixWord ++ tailWord_1772908).sum := by decide
  have hdescent : baseEnd_1772908 < baseStart_1772908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772921 : List Nat := [1, 2, 1, 3, 2, 1, 2, 5, 5]
def baseStart_1772921 : Nat := 118140960795 + 1772921 * 2 ^ 59
def prefixEnd_1772921 : Nat := 4983230072969 + 3 ^ 40 * 1772921 * 2
def baseEnd_1772921 : Nat := 202302363433325149363109

theorem tailTrace_1772921 : CollatzResearch.WordTrace tailWord_1772921 prefixEnd_1772921 202302363433325149363109 := by
  unfold tailWord_1772921
  simp only [CollatzResearch.WordTrace]
  refine ⟨64663741210017482645502617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43109160806678321763668411 64663741210017482645502617)
  ·
    refine ⟨48497805907513111984126963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64663741210017482645502617 48497805907513111984126963)
    ·
      refine ⟨72746708861269667976190445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48497805907513111984126963 72746708861269667976190445)
      ·
        refine ⟨27280015822976125491071417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72746708861269667976190445 27280015822976125491071417)
        ·
          refine ⟨20460011867232094118303563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27280015822976125491071417 20460011867232094118303563)
          ·
            refine ⟨30690017800848141177455345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20460011867232094118303563 30690017800848141177455345)
            ·
              refine ⟨23017513350636105883091509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30690017800848141177455345 23017513350636105883091509)
              ·
                refine ⟨2157891876622134926539829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23017513350636105883091509 2157891876622134926539829)
                ·
                  refine ⟨202302363433325149363109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2157891876622134926539829 202302363433325149363109)
                  ·
                    rfl

theorem cell22_1772921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 5, 5].length) (baseStart_1772921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1772921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1772921 prefixEnd_1772921 := by exact prefixLift 1772921
  have htrace : WordTrace (prefixWord ++ tailWord_1772921) baseStart_1772921 baseEnd_1772921 := by
    simpa [prefixWord, tailWord_1772921, baseEnd_1772921] using wordTrace_append hprefix tailTrace_1772921
  have hstable : (prefixWord ++ tailWord_1772921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772921).length < 2 ^ (prefixWord ++ tailWord_1772921).sum := by decide
  have hdescent : baseEnd_1772921 < baseStart_1772921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772951 : List Nat := [1, 1, 3, 3, 1, 1, 1, 2, 5, 4]
def baseStart_1772951 : Nat := 118140960795 + 1772951 * 2 ^ 59
def prefixEnd_1772951 : Nat := 4983230072969 + 3 ^ 40 * 1772951 * 2
def baseEnd_1772951 : Nat := 606917359913065369839235

theorem tailTrace_1772951 : CollatzResearch.WordTrace tailWord_1772951 prefixEnd_1772951 606917359913065369839235 := by
  unfold tailWord_1772951
  simp only [CollatzResearch.WordTrace]
  refine ⟨64664835399908797769094707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43109890266605865179396471 64664835399908797769094707)
  ·
    refine ⟨96997253099863196653642061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64664835399908797769094707 96997253099863196653642061)
    ·
      refine ⟨36373969912448698745115773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96997253099863196653642061 36373969912448698745115773)
      ·
        refine ⟨13640238717168262029418415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36373969912448698745115773 13640238717168262029418415)
        ·
          refine ⟨20460358075752393044127623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13640238717168262029418415 20460358075752393044127623)
          ·
            refine ⟨30690537113628589566191435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20460358075752393044127623 30690537113628589566191435)
            ·
              refine ⟨46035805670442884349287153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30690537113628589566191435 46035805670442884349287153)
              ·
                refine ⟨34526854252832163261965365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46035805670442884349287153 34526854252832163261965365)
                ·
                  refine ⟨3236892586203015305809253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34526854252832163261965365 3236892586203015305809253)
                  ·
                    refine ⟨606917359913065369839235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3236892586203015305809253 606917359913065369839235)
                    ·
                      rfl

theorem cell22_1772951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 5, 4].length) (baseStart_1772951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1772951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1772951 prefixEnd_1772951 := by exact prefixLift 1772951
  have htrace : WordTrace (prefixWord ++ tailWord_1772951) baseStart_1772951 baseEnd_1772951 := by
    simpa [prefixWord, tailWord_1772951, baseEnd_1772951] using wordTrace_append hprefix tailTrace_1772951
  have hstable : (prefixWord ++ tailWord_1772951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772951).length < 2 ^ (prefixWord ++ tailWord_1772951).sum := by decide
  have hdescent : baseEnd_1772951 < baseStart_1772951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773013 : List Nat := [1, 3, 2, 3, 1, 1, 1, 4, 2, 4]
def baseStart_1773013 : Nat := 118140960795 + 1773013 * 2 ^ 59
def prefixEnd_1773013 : Nat := 4983230072969 + 3 ^ 40 * 1773013 * 2
def baseEnd_1773013 : Nat := 606938583780117874789045

theorem tailTrace_1773013 : CollatzResearch.WordTrace tailWord_1773013 prefixEnd_1773013 606938583780117874789045 := by
  unfold tailWord_1773013
  simp only [CollatzResearch.WordTrace]
  refine ⟨64667096725684182357851693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43111397817122788238567795 64667096725684182357851693)
  ·
    refine ⟨24250161272131568384194385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64667096725684182357851693 24250161272131568384194385)
    ·
      refine ⟨18187620954098676288145789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24250161272131568384194385 18187620954098676288145789)
      ·
        refine ⟨6820357857787003608054671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18187620954098676288145789 6820357857787003608054671)
        ·
          refine ⟨10230536786680505412082007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6820357857787003608054671 10230536786680505412082007)
          ·
            refine ⟨15345805180020758118123011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10230536786680505412082007 15345805180020758118123011)
            ·
              refine ⟨23018707770031137177184517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15345805180020758118123011 23018707770031137177184517)
              ·
                refine ⟨4316007706880838220722097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23018707770031137177184517 4316007706880838220722097)
                ·
                  refine ⟨3237005780160628665541573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4316007706880838220722097 3237005780160628665541573)
                  ·
                    refine ⟨606938583780117874789045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3237005780160628665541573 606938583780117874789045)
                    ·
                      rfl

theorem cell22_1773013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_1773013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1773013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1773013 prefixEnd_1773013 := by exact prefixLift 1773013
  have htrace : WordTrace (prefixWord ++ tailWord_1773013) baseStart_1773013 baseEnd_1773013 := by
    simpa [prefixWord, tailWord_1773013, baseEnd_1773013] using wordTrace_append hprefix tailTrace_1773013
  have hstable : (prefixWord ++ tailWord_1773013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773013).length < 2 ^ (prefixWord ++ tailWord_1773013).sum := by decide
  have hdescent : baseEnd_1773013 < baseStart_1773013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773017 : List Nat := [1, 2, 1, 2, 4, 4, 2, 2, 4]
def baseStart_1773017 : Nat := 118140960795 + 1773017 * 2 ^ 59
def prefixEnd_1773017 : Nat := 4983230072969 + 3 ^ 40 * 1773017 * 2
def baseEnd_1773017 : Nat := 202313317687287732563011

theorem tailTrace_1773017 : CollatzResearch.WordTrace tailWord_1773017 prefixEnd_1773017 202313317687287732563011 := by
  unfold tailWord_1773017
  simp only [CollatzResearch.WordTrace]
  refine ⟨64667242617669691040997305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43111495078446460693998203 64667242617669691040997305)
  ·
    refine ⟨48500431963252268280747979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64667242617669691040997305 48500431963252268280747979)
    ·
      refine ⟨72750647944878402421121969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48500431963252268280747979 72750647944878402421121969)
      ·
        refine ⟨54562985958658801815841477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72750647944878402421121969 54562985958658801815841477)
        ·
          refine ⟨10230559867248525340470277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54562985958658801815841477 10230559867248525340470277)
          ·
            refine ⟨1918229975109098501338177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10230559867248525340470277 1918229975109098501338177)
            ·
              refine ⟨1438672481331823876003633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1918229975109098501338177 1438672481331823876003633)
              ·
                refine ⟨1079004360998867907002725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1438672481331823876003633 1079004360998867907002725)
                ·
                  refine ⟨202313317687287732563011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1079004360998867907002725 202313317687287732563011)
                  ·
                    rfl

theorem cell22_1773017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 2, 4].length) (baseStart_1773017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1773017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1773017 prefixEnd_1773017 := by exact prefixLift 1773017
  have htrace : WordTrace (prefixWord ++ tailWord_1773017) baseStart_1773017 baseEnd_1773017 := by
    simpa [prefixWord, tailWord_1773017, baseEnd_1773017] using wordTrace_append hprefix tailTrace_1773017
  have hstable : (prefixWord ++ tailWord_1773017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773017).length < 2 ^ (prefixWord ++ tailWord_1773017).sum := by decide
  have hdescent : baseEnd_1773017 < baseStart_1773017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773077 : List Nat := [1, 3, 2, 1, 3, 2, 2, 4, 1, 3]
def baseStart_1773077 : Nat := 118140960795 + 1773077 * 2 ^ 59
def prefixEnd_1773077 : Nat := 4983230072969 + 3 ^ 40 * 1773077 * 2
def baseEnd_1773077 : Nat := 606960492288043041188849

theorem tailTrace_1773077 : CollatzResearch.WordTrace tailWord_1773077 prefixEnd_1773077 606960492288043041188849 := by
  unfold tailWord_1773077
  simp only [CollatzResearch.WordTrace]
  refine ⟨64669430997452321288181485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43112953998301547525454323 64669430997452321288181485)
  ·
    refine ⟨24251036624044620483068057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64669430997452321288181485 24251036624044620483068057)
    ·
      refine ⟨18188277468033465362301043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24251036624044620483068057 18188277468033465362301043)
      ·
        refine ⟨27282416202050198043451565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18188277468033465362301043 27282416202050198043451565)
        ·
          refine ⟨10230906075768824266294337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27282416202050198043451565 10230906075768824266294337)
          ·
            refine ⟨7673179556826618199720753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10230906075768824266294337 7673179556826618199720753)
            ·
              refine ⟨5754884667619963649790565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7673179556826618199720753 5754884667619963649790565)
              ·
                refine ⟨1079040875178743184335731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5754884667619963649790565 1079040875178743184335731)
                ·
                  refine ⟨1618561312768114776503597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1079040875178743184335731 1618561312768114776503597)
                  ·
                    refine ⟨606960492288043041188849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1618561312768114776503597 606960492288043041188849)
                    ·
                      rfl

theorem cell22_1773077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 4, 1, 3].length) (baseStart_1773077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1773077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1773077 prefixEnd_1773077 := by exact prefixLift 1773077
  have htrace : WordTrace (prefixWord ++ tailWord_1773077) baseStart_1773077 baseEnd_1773077 := by
    simpa [prefixWord, tailWord_1773077, baseEnd_1773077] using wordTrace_append hprefix tailTrace_1773077
  have hstable : (prefixWord ++ tailWord_1773077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773077).length < 2 ^ (prefixWord ++ tailWord_1773077).sum := by decide
  have hdescent : baseEnd_1773077 < baseStart_1773077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773193 : List Nat := [1, 2, 1, 1, 4, 1, 3, 1, 2, 6]
def baseStart_1773193 : Nat := 118140960795 + 1773193 * 2 ^ 59
def prefixEnd_1773193 : Nat := 4983230072969 + 3 ^ 40 * 1773193 * 2
def baseEnd_1773193 : Nat := 607000201458657405288493

theorem tailTrace_1773193 : CollatzResearch.WordTrace tailWord_1773193 prefixEnd_1773193 607000201458657405288493 := by
  unfold tailWord_1773193
  simp only [CollatzResearch.WordTrace]
  refine ⟨64673661865032073099404233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43115774576688048732936155 64673661865032073099404233)
  ·
    refine ⟨48505246398774054824553175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64673661865032073099404233 48505246398774054824553175)
    ·
      refine ⟨72757869598161082236829763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48505246398774054824553175 72757869598161082236829763)
      ·
        refine ⟨109136804397241623355244645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72757869598161082236829763 109136804397241623355244645)
        ·
          refine ⟨20463150824482804379108371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109136804397241623355244645 20463150824482804379108371)
          ·
            refine ⟨30694726236724206568662557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20463150824482804379108371 30694726236724206568662557)
            ·
              refine ⟨11510522338771577463248459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30694726236724206568662557 11510522338771577463248459)
              ·
                refine ⟨17265783508157366194872689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11510522338771577463248459 17265783508157366194872689)
                ·
                  refine ⟨12949337631118024646154517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17265783508157366194872689 12949337631118024646154517)
                  ·
                    refine ⟨607000201458657405288493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12949337631118024646154517 607000201458657405288493)
                    ·
                      rfl

theorem cell22_1773193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 6].length) (baseStart_1773193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1773193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1773193 prefixEnd_1773193 := by exact prefixLift 1773193
  have htrace : WordTrace (prefixWord ++ tailWord_1773193) baseStart_1773193 baseEnd_1773193 := by
    simpa [prefixWord, tailWord_1773193, baseEnd_1773193] using wordTrace_append hprefix tailTrace_1773193
  have hstable : (prefixWord ++ tailWord_1773193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773193).length < 2 ^ (prefixWord ++ tailWord_1773193).sum := by decide
  have hdescent : baseEnd_1773193 < baseStart_1773193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773195 : List Nat := [1, 1, 1, 1, 4, 1, 4, 3, 3, 3]
def baseStart_1773195 : Nat := 118140960795 + 1773195 * 2 ^ 59
def prefixEnd_1773195 : Nat := 4983230072969 + 3 ^ 40 * 1773195 * 2
def baseEnd_1773195 : Nat := 607000886099530066738487

theorem tailTrace_1773195 : CollatzResearch.WordTrace tailWord_1773195 prefixEnd_1773195 607000886099530066738487 := by
  unfold tailWord_1773195
  simp only [CollatzResearch.WordTrace]
  refine ⟨64673734811024827440977039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43115823207349884960651359 64673734811024827440977039)
  ·
    refine ⟨97010602216537241161465559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64673734811024827440977039 97010602216537241161465559)
    ·
      refine ⟨145515903324805861742198339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97010602216537241161465559 145515903324805861742198339)
      ·
        refine ⟨218273854987208792613297509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145515903324805861742198339 218273854987208792613297509)
        ·
          refine ⟨40926347810101648614993283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 218273854987208792613297509 40926347810101648614993283)
          ·
            refine ⟨61389521715152472922489925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40926347810101648614993283 61389521715152472922489925)
            ·
              refine ⟨11510535321591088672966861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61389521715152472922489925 11510535321591088672966861)
              ·
                refine ⟨4316450745596658252362573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11510535321591088672966861 4316450745596658252362573)
                ·
                  refine ⟨1618669029598746844635965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4316450745596658252362573 1618669029598746844635965)
                  ·
                    refine ⟨607000886099530066738487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1618669029598746844635965 607000886099530066738487)
                    ·
                      rfl

theorem cell22_1773195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3, 3, 3].length) (baseStart_1773195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1773195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1773195 prefixEnd_1773195 := by exact prefixLift 1773195
  have htrace : WordTrace (prefixWord ++ tailWord_1773195) baseStart_1773195 baseEnd_1773195 := by
    simpa [prefixWord, tailWord_1773195, baseEnd_1773195] using wordTrace_append hprefix tailTrace_1773195
  have hstable : (prefixWord ++ tailWord_1773195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773195).length < 2 ^ (prefixWord ++ tailWord_1773195).sum := by decide
  have hdescent : baseEnd_1773195 < baseStart_1773195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773242 : List Nat := [3, 1, 1, 1, 2, 6, 1, 2, 5]
def baseStart_1773242 : Nat := 118140960795 + 1773242 * 2 ^ 59
def prefixEnd_1773242 : Nat := 4983230072969 + 3 ^ 40 * 1773242 * 2
def baseEnd_1773242 : Nat := 202338991720012536937781

theorem tailTrace_1773242 : CollatzResearch.WordTrace tailWord_1773242 prefixEnd_1773242 202338991720012536937781 := by
  unfold tailWord_1773242
  simp only [CollatzResearch.WordTrace]
  refine ⟨16168862260463638616984495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43116966027903036311958653 16168862260463638616984495)
  ·
    refine ⟨24253293390695457925476743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16168862260463638616984495 24253293390695457925476743)
    ·
      refine ⟨36379940086043186888215115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24253293390695457925476743 36379940086043186888215115)
      ·
        refine ⟨54569910129064780332322673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36379940086043186888215115 54569910129064780332322673)
        ·
          refine ⟨40927432596798585249242005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54569910129064780332322673 40927432596798585249242005)
          ·
            refine ⟨1918473402974933683558219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 40927432596798585249242005 1918473402974933683558219)
            ·
              refine ⟨2877710104462400525337329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1918473402974933683558219 2877710104462400525337329)
              ·
                refine ⟨2158282578346800394002997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2877710104462400525337329 2158282578346800394002997)
                ·
                  refine ⟨202338991720012536937781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2158282578346800394002997 202338991720012536937781)
                  ·
                    rfl

theorem cell22_1773242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 2, 5].length) (baseStart_1773242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1773242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1773242 prefixEnd_1773242 := by exact prefixLift 1773242
  have htrace : WordTrace (prefixWord ++ tailWord_1773242) baseStart_1773242 baseEnd_1773242 := by
    simpa [prefixWord, tailWord_1773242, baseEnd_1773242] using wordTrace_append hprefix tailTrace_1773242
  have hstable : (prefixWord ++ tailWord_1773242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773242).length < 2 ^ (prefixWord ++ tailWord_1773242).sum := by decide
  have hdescent : baseEnd_1773242 < baseStart_1773242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773253 : List Nat := [1, 3, 1, 1, 1, 1, 2, 2, 10]
def baseStart_1773253 : Nat := 118140960795 + 1773253 * 2 ^ 59
def prefixEnd_1773253 : Nat := 4983230072969 + 3 ^ 40 * 1773253 * 2
def baseEnd_1773253 : Nat := 202340246894945749596103

theorem tailTrace_1773253 : CollatzResearch.WordTrace tailWord_1773253 prefixEnd_1773253 202340246894945749596103 := by
  unfold tailWord_1773253
  simp only [CollatzResearch.WordTrace]
  refine ⟨64675850244814703346588413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43117233496543135564392275 64675850244814703346588413)
  ·
    refine ⟨24253443841805513754970655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64675850244814703346588413 24253443841805513754970655)
    ·
      refine ⟨36380165762708270632455983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24253443841805513754970655 36380165762708270632455983)
      ·
        refine ⟨54570248644062405948683975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36380165762708270632455983 54570248644062405948683975)
        ·
          refine ⟨81855372966093608923025963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54570248644062405948683975 81855372966093608923025963)
          ·
            refine ⟨122783059449140413384538945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81855372966093608923025963 122783059449140413384538945)
            ·
              refine ⟨92087294586855310038404209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122783059449140413384538945 92087294586855310038404209)
              ·
                refine ⟨69065470940141482528803157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92087294586855310038404209 69065470940141482528803157)
                ·
                  refine ⟨202340246894945749596103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 69065470940141482528803157 202340246894945749596103)
                  ·
                    rfl

theorem cell22_1773253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 10].length) (baseStart_1773253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1773253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1773253 prefixEnd_1773253 := by exact prefixLift 1773253
  have htrace : WordTrace (prefixWord ++ tailWord_1773253) baseStart_1773253 baseEnd_1773253 := by
    simpa [prefixWord, tailWord_1773253, baseEnd_1773253] using wordTrace_append hprefix tailTrace_1773253
  have hstable : (prefixWord ++ tailWord_1773253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773253).length < 2 ^ (prefixWord ++ tailWord_1773253).sum := by decide
  have hdescent : baseEnd_1773253 < baseStart_1773253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773272 : List Nat := [2, 1, 2, 2, 3, 1, 4, 2, 1, 4]
def baseStart_1773272 : Nat := 118140960795 + 1773272 * 2 ^ 59
def prefixEnd_1773272 : Nat := 4983230072969 + 3 ^ 40 * 1773272 * 2
def baseEnd_1773272 : Nat := 607027244773127532563251

theorem tailTrace_1773272 : CollatzResearch.WordTrace tailWord_1773272 prefixEnd_1773272 607027244773127532563251 := by
  unfold tailWord_1773272
  simp only [CollatzResearch.WordTrace]
  refine ⟨32338271615872934795765035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43117695487830579727686713 32338271615872934795765035)
  ·
    refine ⟨48507407423809402193647553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32338271615872934795765035 48507407423809402193647553)
    ·
      refine ⟨36380555567857051645235665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48507407423809402193647553 36380555567857051645235665)
      ·
        refine ⟨27285416675892788733926749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36380555567857051645235665 27285416675892788733926749)
        ·
          refine ⟨10232031253459795775222531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27285416675892788733926749 10232031253459795775222531)
          ·
            refine ⟨15348046880189693662833797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10232031253459795775222531 15348046880189693662833797)
            ·
              refine ⟨2877758790035567561781337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15348046880189693662833797 2877758790035567561781337)
              ·
                refine ⟨2158319092526675671336003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2877758790035567561781337 2158319092526675671336003)
                ·
                  refine ⟨3237478638790013507004005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2158319092526675671336003 3237478638790013507004005)
                  ·
                    refine ⟨607027244773127532563251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3237478638790013507004005 607027244773127532563251)
                    ·
                      rfl

theorem cell22_1773272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 2, 1, 4].length) (baseStart_1773272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1773272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1773272 prefixEnd_1773272 := by exact prefixLift 1773272
  have htrace : WordTrace (prefixWord ++ tailWord_1773272) baseStart_1773272 baseEnd_1773272 := by
    simpa [prefixWord, tailWord_1773272, baseEnd_1773272] using wordTrace_append hprefix tailTrace_1773272
  have hstable : (prefixWord ++ tailWord_1773272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773272).length < 2 ^ (prefixWord ++ tailWord_1773272).sum := by decide
  have hdescent : baseEnd_1773272 < baseStart_1773272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773285 : List Nat := [1, 3, 1, 4, 1, 1, 2, 1, 3, 5]
def baseStart_1773285 : Nat := 118140960795 + 1773285 * 2 ^ 59
def prefixEnd_1773285 : Nat := 4983230072969 + 3 ^ 40 * 1773285 * 2
def baseEnd_1773285 : Nat := 607031694938799831988211

theorem tailTrace_1773285 : CollatzResearch.WordTrace tailWord_1773285 prefixEnd_1773285 607031694938799831988211 := by
  unfold tailWord_1773285
  simp only [CollatzResearch.WordTrace]
  refine ⟨64677017380698772811753309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43118011587132515207835539 64677017380698772811753309)
  ·
    refine ⟨24253881517762039804407491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64677017380698772811753309 24253881517762039804407491)
    ·
      refine ⟨36380822276643059706611237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24253881517762039804407491 36380822276643059706611237)
      ·
        refine ⟨6821404176870573694989607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36380822276643059706611237 6821404176870573694989607)
        ·
          refine ⟨10232106265305860542484411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6821404176870573694989607 10232106265305860542484411)
          ·
            refine ⟨15348159397958790813726617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10232106265305860542484411 15348159397958790813726617)
            ·
              refine ⟨11511119548469093110294963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15348159397958790813726617 11511119548469093110294963)
              ·
                refine ⟨17266679322703639665442445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11511119548469093110294963 17266679322703639665442445)
                ·
                  refine ⟨6475004746013864874540917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17266679322703639665442445 6475004746013864874540917)
                  ·
                    refine ⟨607031694938799831988211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6475004746013864874540917 607031694938799831988211)
                    ·
                      rfl

theorem cell22_1773285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 3, 5].length) (baseStart_1773285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1773285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1773285 prefixEnd_1773285 := by exact prefixLift 1773285
  have htrace : WordTrace (prefixWord ++ tailWord_1773285) baseStart_1773285 baseEnd_1773285 := by
    simpa [prefixWord, tailWord_1773285, baseEnd_1773285] using wordTrace_append hprefix tailTrace_1773285
  have hstable : (prefixWord ++ tailWord_1773285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773285).length < 2 ^ (prefixWord ++ tailWord_1773285).sum := by decide
  have hdescent : baseEnd_1773285 < baseStart_1773285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773411 : List Nat := [1, 1, 1, 5, 5, 1, 1, 2, 5]
def baseStart_1773411 : Nat := 118140960795 + 1773411 * 2 ^ 59
def prefixEnd_1773411 : Nat := 4983230072969 + 3 ^ 40 * 1773411 * 2
def baseEnd_1773411 : Nat := 202358275771259167779275

theorem tailTrace_1773411 : CollatzResearch.WordTrace tailWord_1773411 prefixEnd_1773411 202358275771259167779275 := by
  unfold tailWord_1773411
  simp only [CollatzResearch.WordTrace]
  refine ⟨64681612978242296330840087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43121075318828197553893391 64681612978242296330840087)
  ·
    refine ⟨97022419467363444496260131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64681612978242296330840087 97022419467363444496260131)
    ·
      refine ⟨145533629201045166744390197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97022419467363444496260131 145533629201045166744390197)
      ·
        refine ⟨13643777737597984382286581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 145533629201045166744390197 13643777737597984382286581)
        ·
          refine ⟨1279104162899811035839367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13643777737597984382286581 1279104162899811035839367)
          ·
            refine ⟨1918656244349716553759051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1279104162899811035839367 1918656244349716553759051)
            ·
              refine ⟨2877984366524574830638577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1918656244349716553759051 2877984366524574830638577)
              ·
                refine ⟨2158488274893431122978933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2877984366524574830638577 2158488274893431122978933)
                ·
                  refine ⟨202358275771259167779275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2158488274893431122978933 202358275771259167779275)
                  ·
                    rfl

theorem cell22_1773411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 2, 5].length) (baseStart_1773411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1773411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1773411 prefixEnd_1773411 := by exact prefixLift 1773411
  have htrace : WordTrace (prefixWord ++ tailWord_1773411) baseStart_1773411 baseEnd_1773411 := by
    simpa [prefixWord, tailWord_1773411, baseEnd_1773411] using wordTrace_append hprefix tailTrace_1773411
  have hstable : (prefixWord ++ tailWord_1773411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773411).length < 2 ^ (prefixWord ++ tailWord_1773411).sum := by decide
  have hdescent : baseEnd_1773411 < baseStart_1773411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773452 : List Nat := [2, 2, 1, 2, 1, 2, 1, 5, 2, 4]
def baseStart_1773452 : Nat := 118140960795 + 1773452 * 2 ^ 59
def prefixEnd_1773452 : Nat := 4983230072969 + 3 ^ 40 * 1773452 * 2
def baseEnd_1773452 : Nat := 607088862451667063062699

theorem tailTrace_1773452 : CollatzResearch.WordTrace tailWord_1773452 prefixEnd_1773452 607088862451667063062699 := by
  unfold tailWord_1773452
  simp only [CollatzResearch.WordTrace]
  refine ⟨32341554185546880166541305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43122072247395840222055073 32341554185546880166541305)
  ·
    refine ⟨24256165639160160124905979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32341554185546880166541305 24256165639160160124905979)
    ·
      refine ⟨36384248458740240187358969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24256165639160160124905979 36384248458740240187358969)
      ·
        refine ⟨27288186344055180140519227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36384248458740240187358969 27288186344055180140519227)
        ·
          refine ⟨40932279516082770210778841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27288186344055180140519227 40932279516082770210778841)
          ·
            refine ⟨30699209637062077658084131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40932279516082770210778841 30699209637062077658084131)
            ·
              refine ⟨46048814455593116487126197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30699209637062077658084131 46048814455593116487126197)
              ·
                refine ⟨4317076355211854670668081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46048814455593116487126197 4317076355211854670668081)
                ·
                  refine ⟨3237807266408891003001061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4317076355211854670668081 3237807266408891003001061)
                  ·
                    refine ⟨607088862451667063062699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3237807266408891003001061 607088862451667063062699)
                    ·
                      rfl

theorem cell22_1773452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5, 2, 4].length) (baseStart_1773452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1773452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1773452 prefixEnd_1773452 := by exact prefixLift 1773452
  have htrace : WordTrace (prefixWord ++ tailWord_1773452) baseStart_1773452 baseEnd_1773452 := by
    simpa [prefixWord, tailWord_1773452, baseEnd_1773452] using wordTrace_append hprefix tailTrace_1773452
  have hstable : (prefixWord ++ tailWord_1773452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773452).length < 2 ^ (prefixWord ++ tailWord_1773452).sum := by decide
  have hdescent : baseEnd_1773452 < baseStart_1773452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773469 : List Nat := [1, 4, 2, 1, 2, 3, 1, 2, 2, 4]
def baseStart_1773469 : Nat := 118140960795 + 1773469 * 2 ^ 59
def prefixEnd_1773469 : Nat := 4983230072969 + 3 ^ 40 * 1773469 * 2
def baseEnd_1773469 : Nat := 607094681899084685387647

theorem tailTrace_1773469 : CollatzResearch.WordTrace tailWord_1773469 prefixEnd_1773469 607094681899084685387647 := by
  unfold tailWord_1773469
  simp only [CollatzResearch.WordTrace]
  refine ⟨64683728412032172236451461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43122485608021448157634307 64683728412032172236451461)
  ·
    refine ⟨12128199077256032294334649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64683728412032172236451461 12128199077256032294334649)
    ·
      refine ⟨9096149307942024220750987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12128199077256032294334649 9096149307942024220750987)
      ·
        refine ⟨13644223961913036331126481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9096149307942024220750987 13644223961913036331126481)
        ·
          refine ⟨10233167971434777248344861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13644223961913036331126481 10233167971434777248344861)
          ·
            refine ⟨3837437989288041468129323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10233167971434777248344861 3837437989288041468129323)
            ·
              refine ⟨5756156983932062202193985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3837437989288041468129323 5756156983932062202193985)
              ·
                refine ⟨4317117737949046651645489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5756156983932062202193985 4317117737949046651645489)
                ·
                  refine ⟨3237838303461784988734117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4317117737949046651645489 3237838303461784988734117)
                  ·
                    refine ⟨607094681899084685387647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3237838303461784988734117 607094681899084685387647)
                    ·
                      rfl

theorem cell22_1773469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_1773469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1773469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1773469 prefixEnd_1773469 := by exact prefixLift 1773469
  have htrace : WordTrace (prefixWord ++ tailWord_1773469) baseStart_1773469 baseEnd_1773469 := by
    simpa [prefixWord, tailWord_1773469, baseEnd_1773469] using wordTrace_append hprefix tailTrace_1773469
  have hstable : (prefixWord ++ tailWord_1773469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773469).length < 2 ^ (prefixWord ++ tailWord_1773469).sum := by decide
  have hdescent : baseEnd_1773469 < baseStart_1773469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773473 : List Nat := [1, 2, 3, 4, 2, 1, 3, 2, 4]
def baseStart_1773473 : Nat := 118140960795 + 1773473 * 2 ^ 59
def prefixEnd_1773473 : Nat := 4983230072969 + 3 ^ 40 * 1773473 * 2
def baseEnd_1773473 : Nat := 202365350393610002762545

theorem tailTrace_1773473 : CollatzResearch.WordTrace tailWord_1773473 prefixEnd_1773473 202365350393610002762545 := by
  unfold tailWord_1773473
  simp only [CollatzResearch.WordTrace]
  refine ⟨64683874304017680919597073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43122582869345120613064715 64683874304017680919597073)
  ·
    refine ⟨48512905728013260689697805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64683874304017680919597073 48512905728013260689697805)
    ·
      refine ⟨18192339648004972758636677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48512905728013260689697805 18192339648004972758636677)
      ·
        refine ⟨3411063684000932392244377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18192339648004972758636677 3411063684000932392244377)
        ·
          refine ⟨2558297763000699294183283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3411063684000932392244377 2558297763000699294183283)
          ·
            refine ⟨3837446644501048941274925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2558297763000699294183283 3837446644501048941274925)
            ·
              refine ⟨1439042491687893352978097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3837446644501048941274925 1439042491687893352978097)
              ·
                refine ⟨1079281868765920014733573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1439042491687893352978097 1079281868765920014733573)
                ·
                  refine ⟨202365350393610002762545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1079281868765920014733573 202365350393610002762545)
                  ·
                    rfl

theorem cell22_1773473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 2, 4].length) (baseStart_1773473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1773473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1773473 prefixEnd_1773473 := by exact prefixLift 1773473
  have htrace : WordTrace (prefixWord ++ tailWord_1773473) baseStart_1773473 baseEnd_1773473 := by
    simpa [prefixWord, tailWord_1773473, baseEnd_1773473] using wordTrace_append hprefix tailTrace_1773473
  have hstable : (prefixWord ++ tailWord_1773473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773473).length < 2 ^ (prefixWord ++ tailWord_1773473).sum := by decide
  have hdescent : baseEnd_1773473 < baseStart_1773473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773527 : List Nat := [1, 1, 3, 2, 1, 1, 4, 2, 2, 5]
def baseStart_1773527 : Nat := 118140960795 + 1773527 * 2 ^ 59
def prefixEnd_1773527 : Nat := 4983230072969 + 3 ^ 40 * 1773527 * 2
def baseEnd_1773527 : Nat := 607114536484391867437469

theorem tailTrace_1773527 : CollatzResearch.WordTrace tailWord_1773527 prefixEnd_1773527 607114536484391867437469 := by
  unfold tailWord_1773527
  simp only [CollatzResearch.WordTrace]
  refine ⟨64685843845822048142062835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43123895897214698761375223 64685843845822048142062835)
  ·
    refine ⟨97028765768733072213094253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64685843845822048142062835 97028765768733072213094253)
    ·
      refine ⟨36385787163274902079910345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97028765768733072213094253 36385787163274902079910345)
      ·
        refine ⟨27289340372456176559932759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36385787163274902079910345 27289340372456176559932759)
        ·
          refine ⟨40934010558684264839899139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27289340372456176559932759 40934010558684264839899139)
          ·
            refine ⟨61401015838026397259848709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40934010558684264839899139 61401015838026397259848709)
            ·
              refine ⟨11512690469629949486221633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61401015838026397259848709 11512690469629949486221633)
              ·
                refine ⟨8634517852222462114666225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11512690469629949486221633 8634517852222462114666225)
                ·
                  refine ⟨6475888389166846585999669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8634517852222462114666225 6475888389166846585999669)
                  ·
                    refine ⟨607114536484391867437469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6475888389166846585999669 607114536484391867437469)
                    ·
                      rfl

theorem cell22_1773527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2, 5].length) (baseStart_1773527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1773527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1773527 prefixEnd_1773527 := by exact prefixLift 1773527
  have htrace : WordTrace (prefixWord ++ tailWord_1773527) baseStart_1773527 baseEnd_1773527 := by
    simpa [prefixWord, tailWord_1773527, baseEnd_1773527] using wordTrace_append hprefix tailTrace_1773527
  have hstable : (prefixWord ++ tailWord_1773527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773527).length < 2 ^ (prefixWord ++ tailWord_1773527).sum := by decide
  have hdescent : baseEnd_1773527 < baseStart_1773527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773591 : List Nat := [1, 1, 3, 5, 2, 1, 2, 1, 6]
def baseStart_1773591 : Nat := 118140960795 + 1773591 * 2 ^ 59
def prefixEnd_1773591 : Nat := 4983230072969 + 3 ^ 40 * 1773591 * 2
def baseEnd_1773591 : Nat := 202378814997439011279091

theorem tailTrace_1773591 : CollatzResearch.WordTrace tailWord_1773591 prefixEnd_1773591 202378814997439011279091 := by
  unfold tailWord_1773591
  simp only [CollatzResearch.WordTrace]
  refine ⟨64688178117590187072392627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43125452078393458048261751 64688178117590187072392627)
  ·
    refine ⟨97032267176385280608588941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64688178117590187072392627 97032267176385280608588941)
    ·
      refine ⟨36387100191144480228220853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97032267176385280608588941 36387100191144480228220853)
      ·
        refine ⟨3411290642919795021395705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36387100191144480228220853 3411290642919795021395705)
        ·
          refine ⟨2558467982189846266046779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3411290642919795021395705 2558467982189846266046779)
          ·
            refine ⟨3837701973284769399070169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2558467982189846266046779 3837701973284769399070169)
            ·
              refine ⟨2878276479963577049302627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3837701973284769399070169 2878276479963577049302627)
              ·
                refine ⟨4317414719945365573953941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2878276479963577049302627 4317414719945365573953941)
                ·
                  refine ⟨202378814997439011279091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4317414719945365573953941 202378814997439011279091)
                  ·
                    rfl

theorem cell22_1773591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 1, 6].length) (baseStart_1773591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1773591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1773591 prefixEnd_1773591 := by exact prefixLift 1773591
  have htrace : WordTrace (prefixWord ++ tailWord_1773591) baseStart_1773591 baseEnd_1773591 := by
    simpa [prefixWord, tailWord_1773591, baseEnd_1773591] using wordTrace_append hprefix tailTrace_1773591
  have hstable : (prefixWord ++ tailWord_1773591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773591).length < 2 ^ (prefixWord ++ tailWord_1773591).sum := by decide
  have hdescent : baseEnd_1773591 < baseStart_1773591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773619 : List Nat := [1, 1, 1, 2, 4, 1, 6, 6]
def baseStart_1773619 : Nat := 118140960795 + 1773619 * 2 ^ 59
def prefixEnd_1773619 : Nat := 4983230072969 + 3 ^ 40 * 1773619 * 2
def baseEnd_1773619 : Nat := 67460669996059366015243

theorem tailTrace_1773619 : CollatzResearch.WordTrace tailWord_1773619 prefixEnd_1773619 67460669996059366015243 := by
  unfold tailWord_1773619
  simp only [CollatzResearch.WordTrace]
  refine ⟨64689199361488747854411911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43126132907659165236274607 64689199361488747854411911)
  ·
    refine ⟨97033799042233121781617867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64689199361488747854411911 97033799042233121781617867)
    ·
      refine ⟨145550698563349682672426801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97033799042233121781617867 145550698563349682672426801)
      ·
        refine ⟨109163023922512262004320101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145550698563349682672426801 109163023922512262004320101)
        ·
          refine ⟨20468066985471049125810019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109163023922512262004320101 20468066985471049125810019)
          ·
            refine ⟨30702100478206573688715029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20468066985471049125810019 30702100478206573688715029)
            ·
              refine ⟨1439160959915933141658517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30702100478206573688715029 1439160959915933141658517)
              ·
                refine ⟨67460669996059366015243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1439160959915933141658517 67460669996059366015243)
                ·
                  rfl

theorem cell22_1773619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 6].length) (baseStart_1773619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1773619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1773619 prefixEnd_1773619 := by exact prefixLift 1773619
  have htrace : WordTrace (prefixWord ++ tailWord_1773619) baseStart_1773619 baseEnd_1773619 := by
    simpa [prefixWord, tailWord_1773619, baseEnd_1773619] using wordTrace_append hprefix tailTrace_1773619
  have hstable : (prefixWord ++ tailWord_1773619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773619).length < 2 ^ (prefixWord ++ tailWord_1773619).sum := by decide
  have hdescent : baseEnd_1773619 < baseStart_1773619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773625 : List Nat := [1, 2, 1, 5, 4, 1, 1, 3, 4]
def baseStart_1773625 : Nat := 118140960795 + 1773625 * 2 ^ 59
def prefixEnd_1773625 : Nat := 4983230072969 + 3 ^ 40 * 1773625 * 2
def baseEnd_1773625 : Nat := 202382694629050759495723

theorem tailTrace_1773625 : CollatzResearch.WordTrace tailWord_1773625 prefixEnd_1773625 202382694629050759495723 := by
  unfold tailWord_1773625
  simp only [CollatzResearch.WordTrace]
  refine ⟨64689418199467010879130329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43126278799644673919420219 64689418199467010879130329)
  ·
    refine ⟨48517063649600258159347747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64689418199467010879130329 48517063649600258159347747)
    ·
      refine ⟨72775595474400387239021621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48517063649600258159347747 72775595474400387239021621)
      ·
        refine ⟨6822712075725036303658277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72775595474400387239021621 6822712075725036303658277)
        ·
          refine ⟨1279258514198444306935927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6822712075725036303658277 1279258514198444306935927)
          ·
            refine ⟨1918887771297666460403891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1279258514198444306935927 1918887771297666460403891)
            ·
              refine ⟨2878331656946499690605837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1918887771297666460403891 2878331656946499690605837)
              ·
                refine ⟨1079374371354937383977189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2878331656946499690605837 1079374371354937383977189)
                ·
                  refine ⟨202382694629050759495723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1079374371354937383977189 202382694629050759495723)
                  ·
                    rfl

theorem cell22_1773625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 3, 4].length) (baseStart_1773625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1773625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1773625 prefixEnd_1773625 := by exact prefixLift 1773625
  have htrace : WordTrace (prefixWord ++ tailWord_1773625) baseStart_1773625 baseEnd_1773625 := by
    simpa [prefixWord, tailWord_1773625, baseEnd_1773625] using wordTrace_append hprefix tailTrace_1773625
  have hstable : (prefixWord ++ tailWord_1773625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773625).length < 2 ^ (prefixWord ++ tailWord_1773625).sum := by decide
  have hdescent : baseEnd_1773625 < baseStart_1773625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773638 : List Nat := [6, 1, 1, 1, 1, 1, 3, 2, 2, 4]
def baseStart_1773638 : Nat := 118140960795 + 1773638 * 2 ^ 59
def prefixEnd_1773638 : Nat := 4983230072969 + 3 ^ 40 * 1773638 * 2
def baseEnd_1773638 : Nat := 607152534052824577912129

theorem tailTrace_1773638 : CollatzResearch.WordTrace tailWord_1773638 prefixEnd_1773638 607152534052824577912129 := by
  unfold tailWord_1773638
  simp only [CollatzResearch.WordTrace]
  refine ⟨2021559135888122315604799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 43126594898946609399569045 2021559135888122315604799)
  ·
    refine ⟨3032338703832183473407199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2021559135888122315604799 3032338703832183473407199)
    ·
      refine ⟨4548508055748275210110799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3032338703832183473407199 4548508055748275210110799)
      ·
        refine ⟨6822762083622412815166199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4548508055748275210110799 6822762083622412815166199)
        ·
          refine ⟨10234143125433619222749299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6822762083622412815166199 10234143125433619222749299)
          ·
            refine ⟨15351214688150428834123949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10234143125433619222749299 15351214688150428834123949)
            ·
              refine ⟨5756705508056410812796481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15351214688150428834123949 5756705508056410812796481)
              ·
                refine ⟨4317529131042308109597361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5756705508056410812796481 4317529131042308109597361)
                ·
                  refine ⟨3238146848281731082198021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4317529131042308109597361 3238146848281731082198021)
                  ·
                    refine ⟨607152534052824577912129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3238146848281731082198021 607152534052824577912129)
                    ·
                      rfl

theorem cell22_1773638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_1773638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1773638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1773638 prefixEnd_1773638 := by exact prefixLift 1773638
  have htrace : WordTrace (prefixWord ++ tailWord_1773638) baseStart_1773638 baseEnd_1773638 := by
    simpa [prefixWord, tailWord_1773638, baseEnd_1773638] using wordTrace_append hprefix tailTrace_1773638
  have hstable : (prefixWord ++ tailWord_1773638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773638).length < 2 ^ (prefixWord ++ tailWord_1773638).sum := by decide
  have hdescent : baseEnd_1773638 < baseStart_1773638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773820 : List Nat := [2, 2, 2, 1, 4, 3, 1, 1, 3, 3]
def baseStart_1773820 : Nat := 118140960795 + 1773820 * 2 ^ 59
def prefixEnd_1773820 : Nat := 4983230072969 + 3 ^ 40 * 1773820 * 2
def baseEnd_1773820 : Nat := 607214836372236769861571

theorem tailTrace_1773820 : CollatzResearch.WordTrace tailWord_1773820 prefixEnd_1773820 607214836372236769861571 := by
  unfold tailWord_1773820
  simp only [CollatzResearch.WordTrace]
  refine ⟨32348265216880279591239457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43131020289173706121652609 32348265216880279591239457)
  ·
    refine ⟨24261198912660209693429593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32348265216880279591239457 24261198912660209693429593)
    ·
      refine ⟨18195899184495157270072195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24261198912660209693429593 18195899184495157270072195)
      ·
        refine ⟨27293848776742735905108293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18195899184495157270072195 27293848776742735905108293)
        ·
          refine ⟨5117596645639262982207805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27293848776742735905108293 5117596645639262982207805)
          ·
            refine ⟨1919098742114723618327927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5117596645639262982207805 1919098742114723618327927)
            ·
              refine ⟨2878648113172085427491891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1919098742114723618327927 2878648113172085427491891)
              ·
                refine ⟨4317972169758128141237837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2878648113172085427491891 4317972169758128141237837)
                ·
                  refine ⟨1619239563659298052964189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4317972169758128141237837 1619239563659298052964189)
                  ·
                    refine ⟨607214836372236769861571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1619239563659298052964189 607214836372236769861571)
                    ·
                      rfl

theorem cell22_1773820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 1, 3, 3].length) (baseStart_1773820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1773820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1773820 prefixEnd_1773820 := by exact prefixLift 1773820
  have htrace : WordTrace (prefixWord ++ tailWord_1773820) baseStart_1773820 baseEnd_1773820 := by
    simpa [prefixWord, tailWord_1773820, baseEnd_1773820] using wordTrace_append hprefix tailTrace_1773820
  have hstable : (prefixWord ++ tailWord_1773820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773820).length < 2 ^ (prefixWord ++ tailWord_1773820).sum := by decide
  have hdescent : baseEnd_1773820 < baseStart_1773820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773833 : List Nat := [1, 2, 1, 1, 3, 4, 4, 1, 5]
def baseStart_1773833 : Nat := 118140960795 + 1773833 * 2 ^ 59
def prefixEnd_1773833 : Nat := 4983230072969 + 3 ^ 40 * 1773833 * 2
def baseEnd_1773833 : Nat := 202406428845969689762177

theorem tailTrace_1773833 : CollatzResearch.WordTrace tailWord_1773833 prefixEnd_1773833 202406428845969689762177 := by
  unfold tailWord_1773833
  simp only [CollatzResearch.WordTrace]
  refine ⟨64697004582713462402702153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43131336388475641601801435 64697004582713462402702153)
  ·
    refine ⟨48522753437035096802026615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64697004582713462402702153 48522753437035096802026615)
    ·
      refine ⟨72784130155552645203039923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48522753437035096802026615 72784130155552645203039923)
      ·
        refine ⟨109176195233328967804559885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72784130155552645203039923 109176195233328967804559885)
        ·
          refine ⟨40941073212498362926709957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109176195233328967804559885 40941073212498362926709957)
          ·
            refine ⟨7676451227343443048758117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40941073212498362926709957 7676451227343443048758117)
            ·
              refine ⟨1439334605126895571642147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7676451227343443048758117 1439334605126895571642147)
              ·
                refine ⟨2159001907690343357463221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1439334605126895571642147 2159001907690343357463221)
                ·
                  refine ⟨202406428845969689762177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2159001907690343357463221 202406428845969689762177)
                  ·
                    rfl

theorem cell22_1773833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 1, 5].length) (baseStart_1773833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1773833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1773833 prefixEnd_1773833 := by exact prefixLift 1773833
  have htrace : WordTrace (prefixWord ++ tailWord_1773833) baseStart_1773833 baseEnd_1773833 := by
    simpa [prefixWord, tailWord_1773833, baseEnd_1773833] using wordTrace_append hprefix tailTrace_1773833
  have hstable : (prefixWord ++ tailWord_1773833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773833).length < 2 ^ (prefixWord ++ tailWord_1773833).sum := by decide
  have hdescent : baseEnd_1773833 < baseStart_1773833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773891 : List Nat := [1, 1, 1, 3, 1, 3, 2, 2, 4, 4]
def baseStart_1773891 : Nat := 118140960795 + 1773891 * 2 ^ 59
def prefixEnd_1773891 : Nat := 4983230072969 + 3 ^ 40 * 1773891 * 2
def baseEnd_1773891 : Nat := 607239141123216251336353

theorem tailTrace_1773891 : CollatzResearch.WordTrace tailWord_1773891 prefixEnd_1773891 607239141123216251336353 := by
  unfold tailWord_1773891
  simp only [CollatzResearch.WordTrace]
  refine ⟨64699120016503338308313527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43132746677668892205542351 64699120016503338308313527)
  ·
    refine ⟨97048680024755007462470291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64699120016503338308313527 97048680024755007462470291)
    ·
      refine ⟨145573020037132511193705437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97048680024755007462470291 145573020037132511193705437)
      ·
        refine ⟨54589882513924691697639539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145573020037132511193705437 54589882513924691697639539)
        ·
          refine ⟨81884823770887037546459309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54589882513924691697639539 81884823770887037546459309)
          ·
            refine ⟨30706808914082639079922241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81884823770887037546459309 30706808914082639079922241)
            ·
              refine ⟨23030106685561979309941681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30706808914082639079922241 23030106685561979309941681)
              ·
                refine ⟨17272580014171484482456261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23030106685561979309941681 17272580014171484482456261)
                ·
                  refine ⟨3238608752657153340460549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17272580014171484482456261 3238608752657153340460549)
                  ·
                    refine ⟨607239141123216251336353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3238608752657153340460549 607239141123216251336353)
                    ·
                      rfl

theorem cell22_1773891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 4, 4].length) (baseStart_1773891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1773891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1773891 prefixEnd_1773891 := by exact prefixLift 1773891
  have htrace : WordTrace (prefixWord ++ tailWord_1773891) baseStart_1773891 baseEnd_1773891 := by
    simpa [prefixWord, tailWord_1773891, baseEnd_1773891] using wordTrace_append hprefix tailTrace_1773891
  have hstable : (prefixWord ++ tailWord_1773891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773891).length < 2 ^ (prefixWord ++ tailWord_1773891).sum := by decide
  have hdescent : baseEnd_1773891 < baseStart_1773891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773906 : List Nat := [3, 2, 2, 1, 1, 1, 2, 10]
def baseStart_1773906 : Nat := 118140960795 + 1773906 * 2 ^ 59
def prefixEnd_1773906 : Nat := 4983230072969 + 3 ^ 40 * 1773906 * 2
def baseEnd_1773906 : Nat := 67471586214417912467923

theorem tailTrace_1773906 : CollatzResearch.WordTrace tailWord_1773906 prefixEnd_1773906 67471586214417912467923 := by
  unfold tailWord_1773906
  simp only [CollatzResearch.WordTrace]
  refine ⟨16174916777862248967527393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43133111407632663913406381 16174916777862248967527393)
  ·
    refine ⟨12131187583396686725645545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16174916777862248967527393 12131187583396686725645545)
    ·
      refine ⟨9098390687547515044234159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12131187583396686725645545 9098390687547515044234159)
      ·
        refine ⟨13647586031321272566351239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9098390687547515044234159 13647586031321272566351239)
        ·
          refine ⟨20471379046981908849526859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13647586031321272566351239 20471379046981908849526859)
          ·
            refine ⟨30707068570472863274290289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20471379046981908849526859 30707068570472863274290289)
            ·
              refine ⟨23030301427854647455717717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30707068570472863274290289 23030301427854647455717717)
              ·
                refine ⟨67471586214417912467923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 23030301427854647455717717 67471586214417912467923)
                ·
                  rfl

theorem cell22_1773906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 10].length) (baseStart_1773906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1773906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1773906 prefixEnd_1773906 := by exact prefixLift 1773906
  have htrace : WordTrace (prefixWord ++ tailWord_1773906) baseStart_1773906 baseEnd_1773906 := by
    simpa [prefixWord, tailWord_1773906, baseEnd_1773906] using wordTrace_append hprefix tailTrace_1773906
  have hstable : (prefixWord ++ tailWord_1773906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773906).length < 2 ^ (prefixWord ++ tailWord_1773906).sum := by decide
  have hdescent : baseEnd_1773906 < baseStart_1773906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773908 : List Nat := [2, 4, 1, 1, 2, 3, 1, 1, 1, 6]
def baseStart_1773908 : Nat := 118140960795 + 1773908 * 2 ^ 59
def prefixEnd_1773908 : Nat := 4983230072969 + 3 ^ 40 * 1773908 * 2
def baseEnd_1773908 : Nat := 607244960570633873661301

theorem tailTrace_1773908 : CollatzResearch.WordTrace tailWord_1773908 prefixEnd_1773908 607244960570633873661301 := by
  unfold tailWord_1773908
  simp only [CollatzResearch.WordTrace]
  refine ⟨32349870028720875105841189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43133160038294500141121585 32349870028720875105841189)
  ·
    refine ⟨6065600630385164082345223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32349870028720875105841189 6065600630385164082345223)
    ·
      refine ⟨9098400945577746123517835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6065600630385164082345223 9098400945577746123517835)
      ·
        refine ⟨13647601418366619185276753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9098400945577746123517835 13647601418366619185276753)
        ·
          refine ⟨10235701063774964388957565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13647601418366619185276753 10235701063774964388957565)
          ·
            refine ⟨3838387898915611645859087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10235701063774964388957565 3838387898915611645859087)
            ·
              refine ⟨5757581848373417468788631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3838387898915611645859087 5757581848373417468788631)
              ·
                refine ⟨8636372772560126203182947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5757581848373417468788631 8636372772560126203182947)
                ·
                  refine ⟨12954559158840189304774421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8636372772560126203182947 12954559158840189304774421)
                  ·
                    refine ⟨607244960570633873661301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12954559158840189304774421 607244960570633873661301)
                    ·
                      rfl

theorem cell22_1773908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_1773908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1773908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1773908 prefixEnd_1773908 := by exact prefixLift 1773908
  have htrace : WordTrace (prefixWord ++ tailWord_1773908) baseStart_1773908 baseEnd_1773908 := by
    simpa [prefixWord, tailWord_1773908, baseEnd_1773908] using wordTrace_append hprefix tailTrace_1773908
  have hstable : (prefixWord ++ tailWord_1773908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773908).length < 2 ^ (prefixWord ++ tailWord_1773908).sum := by decide
  have hdescent : baseEnd_1773908 < baseStart_1773908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773918 : List Nat := [4, 4, 2, 1, 2, 1, 1, 2, 5]
def baseStart_1773918 : Nat := 118140960795 + 1773918 * 2 ^ 59
def prefixEnd_1773918 : Nat := 4983230072969 + 3 ^ 40 * 1773918 * 2
def baseEnd_1773918 : Nat := 202416127924999060303757

theorem tailTrace_1773918 : CollatzResearch.WordTrace tailWord_1773918 prefixEnd_1773918 202416127924999060303757 := by
  unfold tailWord_1773918
  simp only [CollatzResearch.WordTrace]
  refine ⟨8087513098425690239943301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43133403191603681279697605 8087513098425690239943301)
  ·
    refine ⟨1516408705954816919989369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8087513098425690239943301 1516408705954816919989369)
    ·
      refine ⟨1137306529466112689992027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1516408705954816919989369 1137306529466112689992027)
      ·
        refine ⟨1705959794199169034988041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1137306529466112689992027 1705959794199169034988041)
        ·
          refine ⟨1279469845649376776241031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1705959794199169034988041 1279469845649376776241031)
          ·
            refine ⟨1919204768474065164361547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1279469845649376776241031 1919204768474065164361547)
            ·
              refine ⟨2878807152711097746542321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1919204768474065164361547 2878807152711097746542321)
              ·
                refine ⟨2159105364533323309906741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2878807152711097746542321 2159105364533323309906741)
                ·
                  refine ⟨202416127924999060303757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2159105364533323309906741 202416127924999060303757)
                  ·
                    rfl

theorem cell22_1773918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_1773918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1773918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1773918 prefixEnd_1773918 := by exact prefixLift 1773918
  have htrace : WordTrace (prefixWord ++ tailWord_1773918) baseStart_1773918 baseEnd_1773918 := by
    simpa [prefixWord, tailWord_1773918, baseEnd_1773918] using wordTrace_append hprefix tailTrace_1773918
  have hstable : (prefixWord ++ tailWord_1773918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773918).length < 2 ^ (prefixWord ++ tailWord_1773918).sum := by decide
  have hdescent : baseEnd_1773918 < baseStart_1773918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773927 : List Nat := [1, 1, 5, 1, 3, 3, 1, 2, 2, 3]
def baseStart_1773927 : Nat := 118140960795 + 1773927 * 2 ^ 59
def prefixEnd_1773927 : Nat := 4983230072969 + 3 ^ 40 * 1773927 * 2
def baseEnd_1773927 : Nat := 607251464658924157436243

theorem tailTrace_1773927 : CollatzResearch.WordTrace tailWord_1773927 prefixEnd_1773927 607251464658924157436243 := by
  unfold tailWord_1773927
  simp only [CollatzResearch.WordTrace]
  refine ⟨64700433044372916456624035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43133622029581944304416023 64700433044372916456624035)
  ·
    refine ⟨97050649566559374684936053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64700433044372916456624035 97050649566559374684936053)
    ·
      refine ⟨9098498396864941376712755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97050649566559374684936053 9098498396864941376712755)
      ·
        refine ⟨13647747595297412065069133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9098498396864941376712755 13647747595297412065069133)
        ·
          refine ⟨5117905348236529524400925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13647747595297412065069133 5117905348236529524400925)
          ·
            refine ⟨1919214505588698571650347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5117905348236529524400925 1919214505588698571650347)
            ·
              refine ⟨2878821758383047857475521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1919214505588698571650347 2878821758383047857475521)
              ·
                refine ⟨2159116318787285893106641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2878821758383047857475521 2159116318787285893106641)
                ·
                  refine ⟨1619337239090464419829981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2159116318787285893106641 1619337239090464419829981)
                  ·
                    refine ⟨607251464658924157436243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1619337239090464419829981 607251464658924157436243)
                    ·
                      rfl

theorem cell22_1773927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_1773927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1773927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1773927 prefixEnd_1773927 := by exact prefixLift 1773927
  have htrace : WordTrace (prefixWord ++ tailWord_1773927) baseStart_1773927 baseEnd_1773927 := by
    simpa [prefixWord, tailWord_1773927, baseEnd_1773927] using wordTrace_append hprefix tailTrace_1773927
  have hstable : (prefixWord ++ tailWord_1773927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773927).length < 2 ^ (prefixWord ++ tailWord_1773927).sum := by decide
  have hdescent : baseEnd_1773927 < baseStart_1773927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773974 : List Nat := [5, 3, 1, 2, 1, 2, 8]
def baseStart_1773974 : Nat := 118140960795 + 1773974 * 2 ^ 59
def prefixEnd_1773974 : Nat := 4983230072969 + 3 ^ 40 * 1773974 * 2
def baseEnd_1773974 : Nat := 22491390878497470426337

theorem tailTrace_1773974 : CollatzResearch.WordTrace tailWord_1773974 prefixEnd_1773974 22491390878497470426337 := by
  unfold tailWord_1773974
  simp only [CollatzResearch.WordTrace]
  refine ⟨4043884204700165217724061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43134764850135095655723317 4043884204700165217724061)
  ·
    refine ⟨1516456576762561956646523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4043884204700165217724061 1516456576762561956646523)
    ·
      refine ⟨2274684865143842934969785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1516456576762561956646523 2274684865143842934969785)
      ·
        refine ⟨1706013648857882201227339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2274684865143842934969785 1706013648857882201227339)
        ·
          refine ⟨2559020473286823301841009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1706013648857882201227339 2559020473286823301841009)
          ·
            refine ⟨1919265354965117476380757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2559020473286823301841009 1919265354965117476380757)
            ·
              refine ⟨22491390878497470426337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1919265354965117476380757 22491390878497470426337)
              ·
                rfl

theorem cell22_1773974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 8].length) (baseStart_1773974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1773974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1773974 prefixEnd_1773974 := by exact prefixLift 1773974
  have htrace : WordTrace (prefixWord ++ tailWord_1773974) baseStart_1773974 baseEnd_1773974 := by
    simpa [prefixWord, tailWord_1773974, baseEnd_1773974] using wordTrace_append hprefix tailTrace_1773974
  have hstable : (prefixWord ++ tailWord_1773974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773974).length < 2 ^ (prefixWord ++ tailWord_1773974).sum := by decide
  have hdescent : baseEnd_1773974 < baseStart_1773974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774030 : List Nat := [4, 1, 1, 1, 2, 1, 1, 7, 4]
def baseStart_1774030 : Nat := 118140960795 + 1774030 * 2 ^ 59
def prefixEnd_1774030 : Nat := 4983230072969 + 3 ^ 40 * 1774030 * 2
def baseEnd_1774030 : Nat := 202428907887955407370309

theorem tailTrace_1774030 : CollatzResearch.WordTrace tailWord_1774030 prefixEnd_1774030 202428907887955407370309 := by
  unfold tailWord_1774030
  simp only [CollatzResearch.WordTrace]
  refine ⟨8088023720374970630952943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43136126508666510031749029 8088023720374970630952943)
  ·
    refine ⟨12132035580562455946429415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8088023720374970630952943 12132035580562455946429415)
    ·
      refine ⟨18198053370843683919644123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12132035580562455946429415 18198053370843683919644123)
      ·
        refine ⟨27297080056265525879466185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18198053370843683919644123 27297080056265525879466185)
        ·
          refine ⟨20472810042199144409599639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27297080056265525879466185 20472810042199144409599639)
          ·
            refine ⟨30709215063298716614399459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20472810042199144409599639 30709215063298716614399459)
            ·
              refine ⟨46063822594948074921599189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30709215063298716614399459 46063822594948074921599189)
              ·
                refine ⟨1079620842069095505974981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 46063822594948074921599189 1079620842069095505974981)
                ·
                  refine ⟨202428907887955407370309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1079620842069095505974981 202428907887955407370309)
                  ·
                    rfl

theorem cell22_1774030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 7, 4].length) (baseStart_1774030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1774030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1774030 prefixEnd_1774030 := by exact prefixLift 1774030
  have htrace : WordTrace (prefixWord ++ tailWord_1774030) baseStart_1774030 baseEnd_1774030 := by
    simpa [prefixWord, tailWord_1774030, baseEnd_1774030] using wordTrace_append hprefix tailTrace_1774030
  have hstable : (prefixWord ++ tailWord_1774030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774030).length < 2 ^ (prefixWord ++ tailWord_1774030).sum := by decide
  have hdescent : baseEnd_1774030 < baseStart_1774030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774047 : List Nat := [1, 1, 2, 3, 3, 2, 4, 2, 4]
def baseStart_1774047 : Nat := 118140960795 + 1774047 * 2 ^ 59
def prefixEnd_1774047 : Nat := 4983230072969 + 3 ^ 40 * 1774047 * 2
def baseEnd_1774047 : Nat := 202430847703761281478625

theorem tailTrace_1774047 : CollatzResearch.WordTrace tailWord_1774047 prefixEnd_1774047 202430847703761281478625 := by
  unfold tailWord_1774047
  simp only [CollatzResearch.WordTrace]
  refine ⟨64704809803938176950992395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43136539869292117967328263 64704809803938176950992395)
  ·
    refine ⟨97057214705907265426488593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64704809803938176950992395 97057214705907265426488593)
    ·
      refine ⟨72792911029430449069866445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97057214705907265426488593 72792911029430449069866445)
      ·
        refine ⟨27297341636036418401199917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72792911029430449069866445 27297341636036418401199917)
        ·
          refine ⟨10236503113513656900449969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27297341636036418401199917 10236503113513656900449969)
          ·
            refine ⟨7677377335135242675337477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10236503113513656900449969 7677377335135242675337477)
            ·
              refine ⟨1439508250337858001625777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7677377335135242675337477 1439508250337858001625777)
              ·
                refine ⟨1079631187753393501219333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1439508250337858001625777 1079631187753393501219333)
                ·
                  refine ⟨202430847703761281478625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1079631187753393501219333 202430847703761281478625)
                  ·
                    rfl

theorem cell22_1774047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 2, 4].length) (baseStart_1774047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1774047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1774047 prefixEnd_1774047 := by exact prefixLift 1774047
  have htrace : WordTrace (prefixWord ++ tailWord_1774047) baseStart_1774047 baseEnd_1774047 := by
    simpa [prefixWord, tailWord_1774047, baseEnd_1774047] using wordTrace_append hprefix tailTrace_1774047
  have hstable : (prefixWord ++ tailWord_1774047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774047).length < 2 ^ (prefixWord ++ tailWord_1774047).sum := by decide
  have hdescent : baseEnd_1774047 < baseStart_1774047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774062 : List Nat := [4, 1, 2, 1, 2, 2, 2, 3, 2, 3]
def baseStart_1774062 : Nat := 118140960795 + 1774062 * 2 ^ 59
def prefixEnd_1774062 : Nat := 4983230072969 + 3 ^ 40 * 1774062 * 2
def baseEnd_1774062 : Nat := 607297677917828805310829

theorem tailTrace_1774062 : CollatzResearch.WordTrace tailWord_1774062 prefixEnd_1774062 607297677917828805310829 := by
  unfold tailWord_1774062
  simp only [CollatzResearch.WordTrace]
  refine ⟨8088169612360479314098555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43136904599255889675192293 8088169612360479314098555)
  ·
    refine ⟨12132254418540718971147833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8088169612360479314098555 12132254418540718971147833)
    ·
      refine ⟨9099190813905539228360875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12132254418540718971147833 9099190813905539228360875)
      ·
        refine ⟨13648786220858308842541313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9099190813905539228360875 13648786220858308842541313)
        ·
          refine ⟨10236589665643731631905985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13648786220858308842541313 10236589665643731631905985)
          ·
            refine ⟨7677442249232798723929489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10236589665643731631905985 7677442249232798723929489)
            ·
              refine ⟨5758081686924599042947117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7677442249232798723929489 5758081686924599042947117)
              ·
                refine ⟨2159280632596724641105169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5758081686924599042947117 2159280632596724641105169)
                ·
                  refine ⟨1619460474447543480828877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2159280632596724641105169 1619460474447543480828877)
                  ·
                    refine ⟨607297677917828805310829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1619460474447543480828877 607297677917828805310829)
                    ·
                      rfl

theorem cell22_1774062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_1774062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1774062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1774062 prefixEnd_1774062 := by exact prefixLift 1774062
  have htrace : WordTrace (prefixWord ++ tailWord_1774062) baseStart_1774062 baseEnd_1774062 := by
    simpa [prefixWord, tailWord_1774062, baseEnd_1774062] using wordTrace_append hprefix tailTrace_1774062
  have hstable : (prefixWord ++ tailWord_1774062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774062).length < 2 ^ (prefixWord ++ tailWord_1774062).sum := by decide
  have hdescent : baseEnd_1774062 < baseStart_1774062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774090 : List Nat := [3, 1, 2, 2, 2, 1, 1, 2, 5, 3]
def baseStart_1774090 : Nat := 118140960795 + 1774090 * 2 ^ 59
def prefixEnd_1774090 : Nat := 4983230072969 + 3 ^ 40 * 1774090 * 2
def baseEnd_1774090 : Nat := 607307262890046065610743

theorem tailTrace_1774090 : CollatzResearch.WordTrace tailWord_1774090 prefixEnd_1774090 607307262890046065610743 := by
  unfold tailWord_1774090
  simp only [CollatzResearch.WordTrace]
  refine ⟨16176594535695598823701931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43137585428521596863205149 16176594535695598823701931)
  ·
    refine ⟨24264891803543398235552897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16176594535695598823701931 24264891803543398235552897)
    ·
      refine ⟨18198668852657548676664673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24264891803543398235552897 18198668852657548676664673)
      ·
        refine ⟨13649001639493161507498505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18198668852657548676664673 13649001639493161507498505)
        ·
          refine ⟨10236751229619871130623879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13649001639493161507498505 10236751229619871130623879)
          ·
            refine ⟨15355126844429806695935819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10236751229619871130623879 15355126844429806695935819)
            ·
              refine ⟨23032690266644710043903729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15355126844429806695935819 23032690266644710043903729)
              ·
                refine ⟨17274517699983532532927797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23032690266644710043903729 17274517699983532532927797)
                ·
                  refine ⟨1619486034373456174961981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17274517699983532532927797 1619486034373456174961981)
                  ·
                    refine ⟨607307262890046065610743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1619486034373456174961981 607307262890046065610743)
                    ·
                      rfl

theorem cell22_1774090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 5, 3].length) (baseStart_1774090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1774090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1774090 prefixEnd_1774090 := by exact prefixLift 1774090
  have htrace : WordTrace (prefixWord ++ tailWord_1774090) baseStart_1774090 baseEnd_1774090 := by
    simpa [prefixWord, tailWord_1774090, baseEnd_1774090] using wordTrace_append hprefix tailTrace_1774090
  have hstable : (prefixWord ++ tailWord_1774090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774090).length < 2 ^ (prefixWord ++ tailWord_1774090).sum := by decide
  have hdescent : baseEnd_1774090 < baseStart_1774090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774141 : List Nat := [1, 4, 1, 3, 2, 3, 1, 3, 1, 3]
def baseStart_1774141 : Nat := 118140960795 + 1774141 * 2 ^ 59
def prefixEnd_1774141 : Nat := 4983230072969 + 3 ^ 40 * 1774141 * 2
def baseEnd_1774141 : Nat := 607324721232298932585587

theorem tailTrace_1774141 : CollatzResearch.WordTrace tailWord_1774141 prefixEnd_1774141 607324721232298932585587 := by
  unfold tailWord_1774141
  simp only [CollatzResearch.WordTrace]
  refine ⟨64708238265597631004914277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43138825510398420669942851 64708238265597631004914277)
  ·
    refine ⟨12132794674799555813421427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64708238265597631004914277 12132794674799555813421427)
    ·
      refine ⟨18199192012199333720132141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12132794674799555813421427 18199192012199333720132141)
      ·
        refine ⟨6824697004574750145049553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18199192012199333720132141 6824697004574750145049553)
        ·
          refine ⟨5118522753431062608787165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6824697004574750145049553 5118522753431062608787165)
          ·
            refine ⟨1919446032536648478295187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5118522753431062608787165 1919446032536648478295187)
            ·
              refine ⟨2879169048804972717442781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1919446032536648478295187 2879169048804972717442781)
              ·
                refine ⟨1079688393301864769041043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2879169048804972717442781 1079688393301864769041043)
                ·
                  refine ⟨1619532589952797153561565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1079688393301864769041043 1619532589952797153561565)
                  ·
                    refine ⟨607324721232298932585587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1619532589952797153561565 607324721232298932585587)
                    ·
                      rfl

theorem cell22_1774141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 3, 1, 3].length) (baseStart_1774141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1774141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1774141 prefixEnd_1774141 := by exact prefixLift 1774141
  have htrace : WordTrace (prefixWord ++ tailWord_1774141) baseStart_1774141 baseEnd_1774141 := by
    simpa [prefixWord, tailWord_1774141, baseEnd_1774141] using wordTrace_append hprefix tailTrace_1774141
  have hstable : (prefixWord ++ tailWord_1774141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774141).length < 2 ^ (prefixWord ++ tailWord_1774141).sum := by decide
  have hdescent : baseEnd_1774141 < baseStart_1774141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774165 : List Nat := [1, 3, 2, 2, 1, 1, 5, 1, 6]
def baseStart_1774165 : Nat := 118140960795 + 1774165 * 2 ^ 59
def prefixEnd_1774165 : Nat := 4983230072969 + 3 ^ 40 * 1774165 * 2
def baseEnd_1774165 : Nat := 202444312307590289995171

theorem tailTrace_1774165 : CollatzResearch.WordTrace tailWord_1774165 prefixEnd_1774165 202444312307590289995171 := by
  unfold tailWord_1774165
  simp only [CollatzResearch.WordTrace]
  refine ⟨64709113617510683103787949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43139409078340455402525299 64709113617510683103787949)
  ·
    refine ⟨24265917606566506163920481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64709113617510683103787949 24265917606566506163920481)
    ·
      refine ⟨18199438204924879622940361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24265917606566506163920481 18199438204924879622940361)
      ·
        refine ⟨13649578653693659717205271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18199438204924879622940361 13649578653693659717205271)
        ·
          refine ⟨20474367980540489575807907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13649578653693659717205271 20474367980540489575807907)
          ·
            refine ⟨30711551970810734363711861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20474367980540489575807907 30711551970810734363711861)
            ·
              refine ⟨2879207997263506346597987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30711551970810734363711861 2879207997263506346597987)
              ·
                refine ⟨4318811995895259519896981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2879207997263506346597987 4318811995895259519896981)
                ·
                  refine ⟨202444312307590289995171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4318811995895259519896981 202444312307590289995171)
                  ·
                    rfl

theorem cell22_1774165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 1, 6].length) (baseStart_1774165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1774165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1774165 prefixEnd_1774165 := by exact prefixLift 1774165
  have htrace : WordTrace (prefixWord ++ tailWord_1774165) baseStart_1774165 baseEnd_1774165 := by
    simpa [prefixWord, tailWord_1774165, baseEnd_1774165] using wordTrace_append hprefix tailTrace_1774165
  have hstable : (prefixWord ++ tailWord_1774165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774165).length < 2 ^ (prefixWord ++ tailWord_1774165).sum := by decide
  have hdescent : baseEnd_1774165 < baseStart_1774165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774180 : List Nat := [2, 3, 1, 1, 2, 2, 2, 3, 1, 5]
def baseStart_1774180 : Nat := 118140960795 + 1774180 * 2 ^ 59
def prefixEnd_1774180 : Nat := 4983230072969 + 3 ^ 40 * 1774180 * 2
def baseEnd_1774180 : Nat := 607338071729315830860467

theorem tailTrace_1774180 : CollatzResearch.WordTrace tailWord_1774180 prefixEnd_1774180 607338071729315830860467 := by
  unfold tailWord_1774180
  simp only [CollatzResearch.WordTrace]
  refine ⟨32354830356228170332791997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43139773808304227110389329 32354830356228170332791997)
  ·
    refine ⟨12133061383585563874796999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32354830356228170332791997 12133061383585563874796999)
    ·
      refine ⟨18199592075378345812195499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12133061383585563874796999 18199592075378345812195499)
      ·
        refine ⟨27299388113067518718293249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18199592075378345812195499 27299388113067518718293249)
        ·
          refine ⟨20474541084800639038719937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27299388113067518718293249 20474541084800639038719937)
          ·
            refine ⟨15355905813600479279039953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20474541084800639038719937 15355905813600479279039953)
            ·
              refine ⟨11516929360200359459279965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15355905813600479279039953 11516929360200359459279965)
              ·
                refine ⟨4318848510075134797229987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11516929360200359459279965 4318848510075134797229987)
                ·
                  refine ⟨6478272765112702195844981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4318848510075134797229987 6478272765112702195844981)
                  ·
                    refine ⟨607338071729315830860467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6478272765112702195844981 607338071729315830860467)
                    ·
                      rfl

theorem cell22_1774180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_1774180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1774180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1774180 prefixEnd_1774180 := by exact prefixLift 1774180
  have htrace : WordTrace (prefixWord ++ tailWord_1774180) baseStart_1774180 baseEnd_1774180 := by
    simpa [prefixWord, tailWord_1774180, baseEnd_1774180] using wordTrace_append hprefix tailTrace_1774180
  have hstable : (prefixWord ++ tailWord_1774180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774180).length < 2 ^ (prefixWord ++ tailWord_1774180).sum := by decide
  have hdescent : baseEnd_1774180 < baseStart_1774180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774212 : List Nat := [2, 3, 2, 1, 3, 1, 2, 2, 2, 4]
def baseStart_1774212 : Nat := 118140960795 + 1774212 * 2 ^ 59
def prefixEnd_1774212 : Nat := 4983230072969 + 3 ^ 40 * 1774212 * 2
def baseEnd_1774212 : Nat := 607349025983278414060369

theorem tailTrace_1774212 : CollatzResearch.WordTrace tailWord_1774212 prefixEnd_1774212 607349025983278414060369 := by
  unfold tailWord_1774212
  simp only [CollatzResearch.WordTrace]
  refine ⟨32355413924170205065374445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43140551898893606753832593 32355413924170205065374445)
  ·
    refine ⟨12133280221563826899515417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32355413924170205065374445 12133280221563826899515417)
    ·
      refine ⟨9099960166172870174636563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12133280221563826899515417 9099960166172870174636563)
      ·
        refine ⟨13649940249259305261954845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9099960166172870174636563 13649940249259305261954845)
        ·
          refine ⟨5118727593472239473233067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13649940249259305261954845 5118727593472239473233067)
          ·
            refine ⟨7678091390208359209849601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5118727593472239473233067 7678091390208359209849601)
            ·
              refine ⟨5758568542656269407387201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7678091390208359209849601 5758568542656269407387201)
              ·
                refine ⟨4318926406992202055540401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5758568542656269407387201 4318926406992202055540401)
                ·
                  refine ⟨3239194805244151541655301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4318926406992202055540401 3239194805244151541655301)
                  ·
                    refine ⟨607349025983278414060369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3239194805244151541655301 607349025983278414060369)
                    ·
                      rfl

theorem cell22_1774212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_1774212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1774212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1774212 prefixEnd_1774212 := by exact prefixLift 1774212
  have htrace : WordTrace (prefixWord ++ tailWord_1774212) baseStart_1774212 baseEnd_1774212 := by
    simpa [prefixWord, tailWord_1774212, baseEnd_1774212] using wordTrace_append hprefix tailTrace_1774212
  have hstable : (prefixWord ++ tailWord_1774212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774212).length < 2 ^ (prefixWord ++ tailWord_1774212).sum := by decide
  have hdescent : baseEnd_1774212 < baseStart_1774212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774259 : List Nat := [1, 1, 1, 2, 3, 4, 1, 5, 1, 3]
def baseStart_1774259 : Nat := 118140960795 + 1774259 * 2 ^ 59
def prefixEnd_1774259 : Nat := 4983230072969 + 3 ^ 40 * 1774259 * 2
def baseEnd_1774259 : Nat := 607365115043785958135225

theorem tailTrace_1774259 : CollatzResearch.WordTrace tailWord_1774259 prefixEnd_1774259 607365115043785958135225 := by
  unfold tailWord_1774259
  simp only [CollatzResearch.WordTrace]
  refine ⟨64712542079170137157709831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43141694719446758105139887 64712542079170137157709831)
  ·
    refine ⟨97068813118755205736564747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64712542079170137157709831 97068813118755205736564747)
    ·
      refine ⟨145603219678132808604847121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97068813118755205736564747 145603219678132808604847121)
      ·
        refine ⟨109202414758599606453635341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145603219678132808604847121 109202414758599606453635341)
        ·
          refine ⟨40950905534474852420113253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109202414758599606453635341 40950905534474852420113253)
          ·
            refine ⟨7678294787714034828771235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40950905534474852420113253 7678294787714034828771235)
            ·
              refine ⟨11517442181571052243156853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7678294787714034828771235 11517442181571052243156853)
              ·
                refine ⟨1079760204522286147795955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11517442181571052243156853 1079760204522286147795955)
                ·
                  refine ⟨1619640306783429221693933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1079760204522286147795955 1619640306783429221693933)
                  ·
                    refine ⟨607365115043785958135225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1619640306783429221693933 607365115043785958135225)
                    ·
                      rfl

theorem cell22_1774259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 5, 1, 3].length) (baseStart_1774259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1774259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1774259 prefixEnd_1774259 := by exact prefixLift 1774259
  have htrace : WordTrace (prefixWord ++ tailWord_1774259) baseStart_1774259 baseEnd_1774259 := by
    simpa [prefixWord, tailWord_1774259, baseEnd_1774259] using wordTrace_append hprefix tailTrace_1774259
  have hstable : (prefixWord ++ tailWord_1774259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774259).length < 2 ^ (prefixWord ++ tailWord_1774259).sum := by decide
  have hdescent : baseEnd_1774259 < baseStart_1774259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774272 : List Nat := [2, 1, 1, 2, 4, 2, 3, 2, 5]
def baseStart_1774272 : Nat := 118140960795 + 1774272 * 2 ^ 59
def prefixEnd_1774272 : Nat := 4983230072969 + 3 ^ 40 * 1774272 * 2
def baseEnd_1774272 : Nat := 202456521736486085853395

theorem tailTrace_1774272 : CollatzResearch.WordTrace tailWord_1774272 prefixEnd_1774272 202456521736486085853395 := by
  unfold tailWord_1774272
  simp only [CollatzResearch.WordTrace]
  refine ⟨32356508114061520188966535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43142010818748693585288713 32356508114061520188966535)
  ·
    refine ⟨48534762171092280283449803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32356508114061520188966535 48534762171092280283449803)
    ·
      refine ⟨72802143256638420425174705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48534762171092280283449803 72802143256638420425174705)
      ·
        refine ⟨54601607442478815318881029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72802143256638420425174705 54601607442478815318881029)
        ·
          refine ⟨10237801395464777872290193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54601607442478815318881029 10237801395464777872290193)
          ·
            refine ⟨7678351046598583404217645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10237801395464777872290193 7678351046598583404217645)
            ·
              refine ⟨2879381642474468776581617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7678351046598583404217645 2879381642474468776581617)
              ·
                refine ⟨2159536231855851582436213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2879381642474468776581617 2159536231855851582436213)
                ·
                  refine ⟨202456521736486085853395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2159536231855851582436213 202456521736486085853395)
                  ·
                    rfl

theorem cell22_1774272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 2, 5].length) (baseStart_1774272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1774272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1774272 prefixEnd_1774272 := by exact prefixLift 1774272
  have htrace : WordTrace (prefixWord ++ tailWord_1774272) baseStart_1774272 baseEnd_1774272 := by
    simpa [prefixWord, tailWord_1774272, baseEnd_1774272] using wordTrace_append hprefix tailTrace_1774272
  have hstable : (prefixWord ++ tailWord_1774272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774272).length < 2 ^ (prefixWord ++ tailWord_1774272).sum := by decide
  have hdescent : baseEnd_1774272 < baseStart_1774272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774276 : List Nat := [2, 3, 3, 1, 1, 2, 2, 4, 1, 3]
def baseStart_1774276 : Nat := 118140960795 + 1774276 * 2 ^ 59
def prefixEnd_1774276 : Nat := 4983230072969 + 3 ^ 40 * 1774276 * 2
def baseEnd_1774276 : Nat := 607370934491203580460173

theorem tailTrace_1774276 : CollatzResearch.WordTrace tailWord_1774276 prefixEnd_1774276 607370934491203580460173 := by
  unfold tailWord_1774276
  simp only [CollatzResearch.WordTrace]
  refine ⟨32356581060054274530539341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43142108080072366040719121 32356581060054274530539341)
  ·
    refine ⟨12133717897520352948952253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32356581060054274530539341 12133717897520352948952253)
    ·
      refine ⟨4550144211570132355857095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12133717897520352948952253 4550144211570132355857095)
      ·
        refine ⟨6825216317355198533785643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4550144211570132355857095 6825216317355198533785643)
        ·
          refine ⟨10237824476032797800678465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6825216317355198533785643 10237824476032797800678465)
          ·
            refine ⟨7678368357024598350508849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10237824476032797800678465 7678368357024598350508849)
            ·
              refine ⟨5758776267768448762881637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7678368357024598350508849 5758776267768448762881637)
              ·
                refine ⟨1079770550206584143040307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5758776267768448762881637 1079770550206584143040307)
                ·
                  refine ⟨1619655825309876214560461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1079770550206584143040307 1619655825309876214560461)
                  ·
                    refine ⟨607370934491203580460173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1619655825309876214560461 607370934491203580460173)
                    ·
                      rfl

theorem cell22_1774276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_1774276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1774276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1774276 prefixEnd_1774276 := by exact prefixLift 1774276
  have htrace : WordTrace (prefixWord ++ tailWord_1774276) baseStart_1774276 baseEnd_1774276 := by
    simpa [prefixWord, tailWord_1774276, baseEnd_1774276] using wordTrace_append hprefix tailTrace_1774276
  have hstable : (prefixWord ++ tailWord_1774276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774276).length < 2 ^ (prefixWord ++ tailWord_1774276).sum := by decide
  have hdescent : baseEnd_1774276 < baseStart_1774276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774315 : List Nat := [1, 1, 1, 1, 2, 4, 1, 3, 3, 5]
def baseStart_1774315 : Nat := 118140960795 + 1774315 * 2 ^ 59
def prefixEnd_1774315 : Nat := 4983230072969 + 3 ^ 40 * 1774315 * 2
def baseEnd_1774315 : Nat := 607384284988220478735053

theorem tailTrace_1774315 : CollatzResearch.WordTrace tailWord_1774315 prefixEnd_1774315 607384284988220478735053 := by
  unfold tailWord_1774315
  simp only [CollatzResearch.WordTrace]
  refine ⟨64714584566967258721748399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43143056377978172481165599 64714584566967258721748399)
  ·
    refine ⟨97071876850450888082622599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64714584566967258721748399 97071876850450888082622599)
    ·
      refine ⟨145607815275676332123933899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97071876850450888082622599 145607815275676332123933899)
      ·
        refine ⟨218411722913514498185900849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145607815275676332123933899 218411722913514498185900849)
        ·
          refine ⟨163808792185135873639425637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218411722913514498185900849 163808792185135873639425637)
          ·
            refine ⟨30714148534712976307392307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 163808792185135873639425637 30714148534712976307392307)
            ·
              refine ⟨46071222802069464461088461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30714148534712976307392307 46071222802069464461088461)
              ·
                refine ⟨17276708550776049172908173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46071222802069464461088461 17276708550776049172908173)
                ·
                  refine ⟨6478765706541018439840565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17276708550776049172908173 6478765706541018439840565)
                  ·
                    refine ⟨607384284988220478735053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6478765706541018439840565 607384284988220478735053)
                    ·
                      rfl

theorem cell22_1774315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3, 5].length) (baseStart_1774315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1774315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1774315 prefixEnd_1774315 := by exact prefixLift 1774315
  have htrace : WordTrace (prefixWord ++ tailWord_1774315) baseStart_1774315 baseEnd_1774315 := by
    simpa [prefixWord, tailWord_1774315, baseEnd_1774315] using wordTrace_append hprefix tailTrace_1774315
  have hstable : (prefixWord ++ tailWord_1774315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774315).length < 2 ^ (prefixWord ++ tailWord_1774315).sum := by decide
  have hdescent : baseEnd_1774315 < baseStart_1774315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774334 : List Nat := [4, 2, 2, 1, 2, 1, 3, 1, 6]
def baseStart_1774334 : Nat := 118140960795 + 1774334 * 2 ^ 59
def prefixEnd_1774334 : Nat := 4983230072969 + 3 ^ 40 * 1774334 * 2
def baseEnd_1774334 : Nat := 202463596358836920836665

theorem tailTrace_1774334 : CollatzResearch.WordTrace tailWord_1774334 prefixEnd_1774334 202463596358836920836665 := by
  unfold tailWord_1774334
  simp only [CollatzResearch.WordTrace]
  refine ⟨8089409694237303120836257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43143518369265616644460037 8089409694237303120836257)
  ·
    refine ⟨6067057270677977340627193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8089409694237303120836257 6067057270677977340627193)
    ·
      refine ⟨4550292953008483005470395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6067057270677977340627193 4550292953008483005470395)
      ·
        refine ⟨6825439429512724508205593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4550292953008483005470395 6825439429512724508205593)
        ·
          refine ⟨5119079572134543381154195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6825439429512724508205593 5119079572134543381154195)
          ·
            refine ⟨7678619358201815071731293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5119079572134543381154195 7678619358201815071731293)
            ·
              refine ⟨2879482259325680651899235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7678619358201815071731293 2879482259325680651899235)
              ·
                refine ⟨4319223388988520977848853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2879482259325680651899235 4319223388988520977848853)
                ·
                  refine ⟨202463596358836920836665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4319223388988520977848853 202463596358836920836665)
                  ·
                    rfl

theorem cell22_1774334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_1774334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1774334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1774334 prefixEnd_1774334 := by exact prefixLift 1774334
  have htrace : WordTrace (prefixWord ++ tailWord_1774334) baseStart_1774334 baseEnd_1774334 := by
    simpa [prefixWord, tailWord_1774334, baseEnd_1774334] using wordTrace_append hprefix tailTrace_1774334
  have hstable : (prefixWord ++ tailWord_1774334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774334).length < 2 ^ (prefixWord ++ tailWord_1774334).sum := by decide
  have hdescent : baseEnd_1774334 < baseStart_1774334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774345 : List Nat := [1, 2, 1, 1, 3, 2, 3, 9]
def baseStart_1774345 : Nat := 118140960795 + 1774345 * 2 ^ 59
def prefixEnd_1774345 : Nat := 4983230072969 + 3 ^ 40 * 1774345 * 2
def baseEnd_1774345 : Nat := 67488283844590044498329

theorem tailTrace_1774345 : CollatzResearch.WordTrace tailWord_1774345 prefixEnd_1774345 67488283844590044498329 := by
  unfold tailWord_1774345
  simp only [CollatzResearch.WordTrace]
  refine ⟨64715678756858573845340489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43143785837905715896893659 64715678756858573845340489)
  ·
    refine ⟨48536759067643930384005367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64715678756858573845340489 48536759067643930384005367)
    ·
      refine ⟨72805138601465895576008051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48536759067643930384005367 72805138601465895576008051)
      ·
        refine ⟨109207707902198843364012077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72805138601465895576008051 109207707902198843364012077)
        ·
          refine ⟨40952890463324566261504529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109207707902198843364012077 40952890463324566261504529)
          ·
            refine ⟨30714667847493424696128397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40952890463324566261504529 30714667847493424696128397)
            ·
              refine ⟨11518000442810034261048149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30714667847493424696128397 11518000442810034261048149)
              ·
                refine ⟨67488283844590044498329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11518000442810034261048149 67488283844590044498329)
                ·
                  rfl

theorem cell22_1774345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 9].length) (baseStart_1774345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1774345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1774345 prefixEnd_1774345 := by exact prefixLift 1774345
  have htrace : WordTrace (prefixWord ++ tailWord_1774345) baseStart_1774345 baseEnd_1774345 := by
    simpa [prefixWord, tailWord_1774345, baseEnd_1774345] using wordTrace_append hprefix tailTrace_1774345
  have hstable : (prefixWord ++ tailWord_1774345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774345).length < 2 ^ (prefixWord ++ tailWord_1774345).sum := by decide
  have hdescent : baseEnd_1774345 < baseStart_1774345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774364 : List Nat := [2, 2, 3, 1, 1, 4, 2, 1, 2, 4]
def baseStart_1774364 : Nat := 118140960795 + 1774364 * 2 ^ 59
def prefixEnd_1774364 : Nat := 4983230072969 + 3 ^ 40 * 1774364 * 2
def baseEnd_1774364 : Nat := 607401058689600684259903

theorem tailTrace_1774364 : CollatzResearch.WordTrace tailWord_1774364 prefixEnd_1774364 607401058689600684259903 := by
  unfold tailWord_1774364
  simp only [CollatzResearch.WordTrace]
  refine ⟨32358185871894870045141073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43144247829193160060188097 32358185871894870045141073)
  ·
    refine ⟨24268639403921152533855805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32358185871894870045141073 24268639403921152533855805)
    ·
      refine ⟨9100739776470432200195927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24268639403921152533855805 9100739776470432200195927)
      ·
        refine ⟨13651109664705648300293891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9100739776470432200195927 13651109664705648300293891)
        ·
          refine ⟨20476664497058472450440837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13651109664705648300293891 20476664497058472450440837)
          ·
            refine ⟨3839374593198463584457657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20476664497058472450440837 3839374593198463584457657)
            ·
              refine ⟨2879530944898847688343243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3839374593198463584457657 2879530944898847688343243)
              ·
                refine ⟨4319296417348271532514865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2879530944898847688343243 4319296417348271532514865)
                ·
                  refine ⟨3239472313011203649386149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4319296417348271532514865 3239472313011203649386149)
                  ·
                    refine ⟨607401058689600684259903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3239472313011203649386149 607401058689600684259903)
                    ·
                      rfl

theorem cell22_1774364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_1774364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1774364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1774364 prefixEnd_1774364 := by exact prefixLift 1774364
  have htrace : WordTrace (prefixWord ++ tailWord_1774364) baseStart_1774364 baseEnd_1774364 := by
    simpa [prefixWord, tailWord_1774364, baseEnd_1774364] using wordTrace_append hprefix tailTrace_1774364
  have hstable : (prefixWord ++ tailWord_1774364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774364).length < 2 ^ (prefixWord ++ tailWord_1774364).sum := by decide
  have hdescent : baseEnd_1774364 < baseStart_1774364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774377 : List Nat := [1, 2, 1, 1, 1, 1, 1, 6, 5, 3]
def baseStart_1774377 : Nat := 118140960795 + 1774377 * 2 ^ 59
def prefixEnd_1774377 : Nat := 4983230072969 + 3 ^ 40 * 1774377 * 2
def baseEnd_1774377 : Nat := 607405508855272983684863

theorem tailTrace_1774377 : CollatzResearch.WordTrace tailWord_1774377 prefixEnd_1774377 607405508855272983684863 := by
  unfold tailWord_1774377
  simp only [CollatzResearch.WordTrace]
  refine ⟨64716845892742643310505385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43144563928495095540336923 64716845892742643310505385)
  ·
    refine ⟨48537634419556982482879039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64716845892742643310505385 48537634419556982482879039)
    ·
      refine ⟨72806451629335473724318559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48537634419556982482879039 72806451629335473724318559)
      ·
        refine ⟨109209677444003210586477839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72806451629335473724318559 109209677444003210586477839)
        ·
          refine ⟨163814516166004815879716759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109209677444003210586477839 163814516166004815879716759)
          ·
            refine ⟨245721774249007223819575139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163814516166004815879716759 245721774249007223819575139)
            ·
              refine ⟨368582661373510835729362709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245721774249007223819575139 368582661373510835729362709)
              ·
                refine ⟨17277312251883320424813877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 368582661373510835729362709 17277312251883320424813877)
                ·
                  refine ⟨1619748023614061289826301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17277312251883320424813877 1619748023614061289826301)
                  ·
                    refine ⟨607405508855272983684863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1619748023614061289826301 607405508855272983684863)
                    ·
                      rfl

theorem cell22_1774377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 5, 3].length) (baseStart_1774377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1774377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1774377 prefixEnd_1774377 := by exact prefixLift 1774377
  have htrace : WordTrace (prefixWord ++ tailWord_1774377) baseStart_1774377 baseEnd_1774377 := by
    simpa [prefixWord, tailWord_1774377, baseEnd_1774377] using wordTrace_append hprefix tailTrace_1774377
  have hstable : (prefixWord ++ tailWord_1774377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774377).length < 2 ^ (prefixWord ++ tailWord_1774377).sum := by decide
  have hdescent : baseEnd_1774377 < baseStart_1774377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774428 : List Nat := [2, 2, 4, 2, 1, 1, 1, 5, 1, 3]
def baseStart_1774428 : Nat := 118140960795 + 1774428 * 2 ^ 59
def prefixEnd_1774428 : Nat := 4983230072969 + 3 ^ 40 * 1774428 * 2
def baseEnd_1774428 : Nat := 607422967197525850659707

theorem tailTrace_1774428 : CollatzResearch.WordTrace tailWord_1774428 prefixEnd_1774428 607422967197525850659707 := by
  unfold tailWord_1774428
  simp only [CollatzResearch.WordTrace]
  refine ⟨32359353007778939510305969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43145804010371919347074625 32359353007778939510305969)
  ·
    refine ⟨24269514755834204632729477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32359353007778939510305969 24269514755834204632729477)
    ·
      refine ⟨4550534016718913368636777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24269514755834204632729477 4550534016718913368636777)
      ·
        refine ⟨3412900512539185026477583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4550534016718913368636777 3412900512539185026477583)
        ·
          refine ⟨5119350768808777539716375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3412900512539185026477583 5119350768808777539716375)
          ·
            refine ⟨7679026153213166309574563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5119350768808777539716375 7679026153213166309574563)
            ·
              refine ⟨11518539229819749464361845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7679026153213166309574563 11518539229819749464361845)
              ·
                refine ⟨1079863052795601512283923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11518539229819749464361845 1079863052795601512283923)
                ·
                  refine ⟨1619794579193402268425885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1079863052795601512283923 1619794579193402268425885)
                  ·
                    refine ⟨607422967197525850659707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1619794579193402268425885 607422967197525850659707)
                    ·
                      rfl

theorem cell22_1774428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_1774428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1774428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1774428 prefixEnd_1774428 := by exact prefixLift 1774428
  have htrace : WordTrace (prefixWord ++ tailWord_1774428) baseStart_1774428 baseEnd_1774428 := by
    simpa [prefixWord, tailWord_1774428, baseEnd_1774428] using wordTrace_append hprefix tailTrace_1774428
  have hstable : (prefixWord ++ tailWord_1774428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774428).length < 2 ^ (prefixWord ++ tailWord_1774428).sum := by decide
  have hdescent : baseEnd_1774428 < baseStart_1774428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774471 : List Nat := [1, 1, 4, 2, 3, 2, 2, 2, 1, 4]
def baseStart_1774471 : Nat := 118140960795 + 1774471 * 2 ^ 59
def prefixEnd_1774471 : Nat := 4983230072969 + 3 ^ 40 * 1774471 * 2
def baseEnd_1774471 : Nat := 607437686976288071834575

theorem tailTrace_1774471 : CollatzResearch.WordTrace tailWord_1774471 prefixEnd_1774471 607437686976288071834575 := by
  unfold tailWord_1774471
  simp only [CollatzResearch.WordTrace]
  refine ⟨64720274354402097364427267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43146849569601398242951511 64720274354402097364427267)
  ·
    refine ⟨97080411531603146046640901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64720274354402097364427267 97080411531603146046640901)
    ·
      refine ⟨18202577162175589883745169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97080411531603146046640901 18202577162175589883745169)
      ·
        refine ⟨13651932871631692412808877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18202577162175589883745169 13651932871631692412808877)
        ·
          refine ⟨5119474826861884654803329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13651932871631692412808877 5119474826861884654803329)
          ·
            refine ⟨3839606120146413491102497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5119474826861884654803329 3839606120146413491102497)
            ·
              refine ⟨2879704590109810118326873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3839606120146413491102497 2879704590109810118326873)
              ·
                refine ⟨2159778442582357588745155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2879704590109810118326873 2159778442582357588745155)
                ·
                  refine ⟨3239667663873536383117733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2159778442582357588745155 3239667663873536383117733)
                  ·
                    refine ⟨607437686976288071834575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3239667663873536383117733 607437686976288071834575)
                    ·
                      rfl

theorem cell22_1774471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 2, 1, 4].length) (baseStart_1774471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1774471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1774471 prefixEnd_1774471 := by exact prefixLift 1774471
  have htrace : WordTrace (prefixWord ++ tailWord_1774471) baseStart_1774471 baseEnd_1774471 := by
    simpa [prefixWord, tailWord_1774471, baseEnd_1774471] using wordTrace_append hprefix tailTrace_1774471
  have hstable : (prefixWord ++ tailWord_1774471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774471).length < 2 ^ (prefixWord ++ tailWord_1774471).sum := by decide
  have hdescent : baseEnd_1774471 < baseStart_1774471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774484 : List Nat := [2, 4, 2, 1, 1, 1, 2, 1, 3, 5]
def baseStart_1774484 : Nat := 118140960795 + 1774484 * 2 ^ 59
def prefixEnd_1774484 : Nat := 4983230072969 + 3 ^ 40 * 1774484 * 2
def baseEnd_1774484 : Nat := 607442137141960371259535

theorem tailTrace_1774484 : CollatzResearch.WordTrace tailWord_1774484 prefixEnd_1774484 607442137141960371259535 := by
  unfold tailWord_1774484
  simp only [CollatzResearch.WordTrace]
  refine ⟨32360374251677500292325253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43147165668903333723100337 32360374251677500292325253)
  ·
    refine ⟨6067570172189531304810985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32360374251677500292325253 6067570172189531304810985)
    ·
      refine ⟨4550677629142148478608239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6067570172189531304810985 4550677629142148478608239)
      ·
        refine ⟨6826016443713222717912359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4550677629142148478608239 6826016443713222717912359)
        ·
          refine ⟨10239024665569834076868539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6826016443713222717912359 10239024665569834076868539)
          ·
            refine ⟨15358536998354751115302809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10239024665569834076868539 15358536998354751115302809)
            ·
              refine ⟨11518902748766063336477107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15358536998354751115302809 11518902748766063336477107)
              ·
                refine ⟨17278354123149095004715661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11518902748766063336477107 17278354123149095004715661)
                ·
                  refine ⟨6479382796180910626768373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17278354123149095004715661 6479382796180910626768373)
                  ·
                    refine ⟨607442137141960371259535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6479382796180910626768373 607442137141960371259535)
                    ·
                      rfl

theorem cell22_1774484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_1774484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1774484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1774484 prefixEnd_1774484 := by exact prefixLift 1774484
  have htrace : WordTrace (prefixWord ++ tailWord_1774484) baseStart_1774484 baseEnd_1774484 := by
    simpa [prefixWord, tailWord_1774484, baseEnd_1774484] using wordTrace_append hprefix tailTrace_1774484
  have hstable : (prefixWord ++ tailWord_1774484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774484).length < 2 ^ (prefixWord ++ tailWord_1774484).sum := by decide
  have hdescent : baseEnd_1774484 < baseStart_1774484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774503 : List Nat := [1, 1, 6, 1, 4, 1, 1, 1, 6]
def baseStart_1774503 : Nat := 118140960795 + 1774503 * 2 ^ 59
def prefixEnd_1774503 : Nat := 4983230072969 + 3 ^ 40 * 1774503 * 2
def baseEnd_1774503 : Nat := 202482880410083551678159

theorem tailTrace_1774503 : CollatzResearch.WordTrace tailWord_1774503 prefixEnd_1774503 202482880410083551678159 := by
  unfold tailWord_1774503
  simp only [CollatzResearch.WordTrace]
  refine ⟨64721441490286166829592163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43147627660190777886394775 64721441490286166829592163)
  ·
    refine ⟨97082162235429250244388245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64721441490286166829592163 97082162235429250244388245)
    ·
      refine ⟨4550726354785746105205699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 97082162235429250244388245 4550726354785746105205699)
      ·
        refine ⟨6826089532178619157808549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4550726354785746105205699 6826089532178619157808549)
        ·
          refine ⟨1279891787283491092089103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6826089532178619157808549 1279891787283491092089103)
          ·
            refine ⟨1919837680925236638133655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1279891787283491092089103 1919837680925236638133655)
            ·
              refine ⟨2879756521387854957200483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1919837680925236638133655 2879756521387854957200483)
              ·
                refine ⟨4319634782081782435800725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2879756521387854957200483 4319634782081782435800725)
                ·
                  refine ⟨202482880410083551678159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4319634782081782435800725 202482880410083551678159)
                  ·
                    rfl

theorem cell22_1774503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 1, 6].length) (baseStart_1774503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1774503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1774503 prefixEnd_1774503 := by exact prefixLift 1774503
  have htrace : WordTrace (prefixWord ++ tailWord_1774503) baseStart_1774503 baseEnd_1774503 := by
    simpa [prefixWord, tailWord_1774503, baseEnd_1774503] using wordTrace_append hprefix tailTrace_1774503
  have hstable : (prefixWord ++ tailWord_1774503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774503).length < 2 ^ (prefixWord ++ tailWord_1774503).sum := by decide
  have hdescent : baseEnd_1774503 < baseStart_1774503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774527 : List Nat := [1, 1, 2, 2, 2, 1, 2, 1, 4, 6]
def baseStart_1774527 : Nat := 118140960795 + 1774527 * 2 ^ 59
def prefixEnd_1774527 : Nat := 4983230072969 + 3 ^ 40 * 1774527 * 2
def baseEnd_1774527 : Nat := 607456856920722592434403

theorem tailTrace_1774527 : CollatzResearch.WordTrace tailWord_1774527 prefixEnd_1774527 607456856920722592434403 := by
  unfold tailWord_1774527
  simp only [CollatzResearch.WordTrace]
  refine ⟨64722316842199218928465835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43148211228132812618977223 64722316842199218928465835)
  ·
    refine ⟨97083475263298828392698753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64722316842199218928465835 97083475263298828392698753)
    ·
      refine ⟨72812606447474121294524065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97083475263298828392698753 72812606447474121294524065)
      ·
        refine ⟨54609454835605590970893049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72812606447474121294524065 54609454835605590970893049)
        ·
          refine ⟨40957091126704193228169787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54609454835605590970893049 40957091126704193228169787)
          ·
            refine ⟨61435636690056289842254681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40957091126704193228169787 61435636690056289842254681)
            ·
              refine ⟨46076727517542217381691011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61435636690056289842254681 46076727517542217381691011)
              ·
                refine ⟨69115091276313326072536517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46076727517542217381691011 69115091276313326072536517)
                ·
                  refine ⟨12959079614308748638600597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69115091276313326072536517 12959079614308748638600597)
                  ·
                    refine ⟨607456856920722592434403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12959079614308748638600597 607456856920722592434403)
                    ·
                      rfl

theorem cell22_1774527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 6].length) (baseStart_1774527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1774527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1774527 prefixEnd_1774527 := by exact prefixLift 1774527
  have htrace : WordTrace (prefixWord ++ tailWord_1774527) baseStart_1774527 baseEnd_1774527 := by
    simpa [prefixWord, tailWord_1774527, baseEnd_1774527] using wordTrace_append hprefix tailTrace_1774527
  have hstable : (prefixWord ++ tailWord_1774527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774527).length < 2 ^ (prefixWord ++ tailWord_1774527).sum := by decide
  have hdescent : baseEnd_1774527 < baseStart_1774527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774563 : List Nat := [1, 1, 1, 6, 1, 1, 3, 4, 1, 3]
def baseStart_1774563 : Nat := 118140960795 + 1774563 * 2 ^ 59
def prefixEnd_1774563 : Nat := 4983230072969 + 3 ^ 40 * 1774563 * 2
def baseEnd_1774563 : Nat := 607469180456430498534293

theorem tailTrace_1774563 : CollatzResearch.WordTrace tailWord_1774563 prefixEnd_1774563 607469180456430498534293 := by
  unfold tailWord_1774563
  simp only [CollatzResearch.WordTrace]
  refine ⟨64723629870068797076776343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43149086580045864717850895 64723629870068797076776343)
  ·
    refine ⟨97085444805103195615164515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64723629870068797076776343 97085444805103195615164515)
    ·
      refine ⟨145628167207654793422746773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97085444805103195615164515 145628167207654793422746773)
      ·
        refine ⟨6826320337858818441691255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 145628167207654793422746773 6826320337858818441691255)
        ·
          refine ⟨10239480506788227662536883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6826320337858818441691255 10239480506788227662536883)
          ·
            refine ⟨15359220760182341493805325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10239480506788227662536883 15359220760182341493805325)
            ·
              refine ⟨5759707785068378060176997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15359220760182341493805325 5759707785068378060176997)
              ·
                refine ⟨1079945209700320886283187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5759707785068378060176997 1079945209700320886283187)
                ·
                  refine ⟨1619917814550481329424781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1079945209700320886283187 1619917814550481329424781)
                  ·
                    refine ⟨607469180456430498534293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1619917814550481329424781 607469180456430498534293)
                    ·
                      rfl

theorem cell22_1774563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 4, 1, 3].length) (baseStart_1774563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1774563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1774563 prefixEnd_1774563 := by exact prefixLift 1774563
  have htrace : WordTrace (prefixWord ++ tailWord_1774563) baseStart_1774563 baseEnd_1774563 := by
    simpa [prefixWord, tailWord_1774563, baseEnd_1774563] using wordTrace_append hprefix tailTrace_1774563
  have hstable : (prefixWord ++ tailWord_1774563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774563).length < 2 ^ (prefixWord ++ tailWord_1774563).sum := by decide
  have hdescent : baseEnd_1774563 < baseStart_1774563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774610 : List Nat := [3, 2, 5, 1, 1, 1, 1, 1, 7]
def baseStart_1774610 : Nat := 118140960795 + 1774610 * 2 ^ 59
def prefixEnd_1774610 : Nat := 4983230072969 + 3 ^ 40 * 1774610 * 2
def baseEnd_1774610 : Nat := 202495089838979347536383

theorem tailTrace_1774610 : CollatzResearch.WordTrace tailWord_1774610 prefixEnd_1774610 202495089838979347536383 := by
  unfold tailWord_1774610
  simp only [CollatzResearch.WordTrace]
  refine ⟨16181336025224631025934321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43150229400599016069158189 16181336025224631025934321)
  ·
    refine ⟨12136002018918473269450741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16181336025224631025934321 12136002018918473269450741)
    ·
      refine ⟨1137750189273606869011007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12136002018918473269450741 1137750189273606869011007)
      ·
        refine ⟨1706625283910410303516511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1137750189273606869011007 1706625283910410303516511)
        ·
          refine ⟨2559937925865615455274767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1706625283910410303516511 2559937925865615455274767)
          ·
            refine ⟨3839906888798423182912151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2559937925865615455274767 3839906888798423182912151)
            ·
              refine ⟨5759860333197634774368227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3839906888798423182912151 5759860333197634774368227)
              ·
                refine ⟨8639790499796452161552341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5759860333197634774368227 8639790499796452161552341)
                ·
                  refine ⟨202495089838979347536383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8639790499796452161552341 202495089838979347536383)
                  ·
                    rfl

theorem cell22_1774610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 7].length) (baseStart_1774610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1774610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1774610 prefixEnd_1774610 := by exact prefixLift 1774610
  have htrace : WordTrace (prefixWord ++ tailWord_1774610) baseStart_1774610 baseEnd_1774610 := by
    simpa [prefixWord, tailWord_1774610, baseEnd_1774610] using wordTrace_append hprefix tailTrace_1774610
  have hstable : (prefixWord ++ tailWord_1774610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774610).length < 2 ^ (prefixWord ++ tailWord_1774610).sum := by decide
  have hdescent : baseEnd_1774610 < baseStart_1774610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774679 : List Nat := [1, 1, 3, 2, 2, 1, 1, 3, 2, 6]
def baseStart_1774679 : Nat := 118140960795 + 1774679 * 2 ^ 59
def prefixEnd_1774679 : Nat := 4983230072969 + 3 ^ 40 * 1774679 * 2
def baseEnd_1774679 : Nat := 607508889627044862633937

theorem tailTrace_1774679 : CollatzResearch.WordTrace tailWord_1774679 prefixEnd_1774679 607508889627044862633937 := by
  unfold tailWord_1774679
  simp only [CollatzResearch.WordTrace]
  refine ⟨64727860737648548887999091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43151907158432365925332727 64727860737648548887999091)
  ·
    refine ⟨97091791106472823331998637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64727860737648548887999091 97091791106472823331998637)
    ·
      refine ⟨36409421664927308749499489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97091791106472823331998637 36409421664927308749499489)
      ·
        refine ⟨27307066248695481562124617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36409421664927308749499489 27307066248695481562124617)
        ·
          refine ⟨20480299686521611171593463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27307066248695481562124617 20480299686521611171593463)
          ·
            refine ⟨30720449529782416757390195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20480299686521611171593463 30720449529782416757390195)
            ·
              refine ⟨46080674294673625136085293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30720449529782416757390195 46080674294673625136085293)
              ·
                refine ⟨17280252860502609426031985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46080674294673625136085293 17280252860502609426031985)
                ·
                  refine ⟨12960189645376957069523989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17280252860502609426031985 12960189645376957069523989)
                  ·
                    refine ⟨607508889627044862633937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12960189645376957069523989 607508889627044862633937)
                    ·
                      rfl

theorem cell22_1774679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 6].length) (baseStart_1774679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1774679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1774679 prefixEnd_1774679 := by exact prefixLift 1774679
  have htrace : WordTrace (prefixWord ++ tailWord_1774679) baseStart_1774679 baseEnd_1774679 := by
    simpa [prefixWord, tailWord_1774679, baseEnd_1774679] using wordTrace_append hprefix tailTrace_1774679
  have hstable : (prefixWord ++ tailWord_1774679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774679).length < 2 ^ (prefixWord ++ tailWord_1774679).sum := by decide
  have hdescent : baseEnd_1774679 < baseStart_1774679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774681 : List Nat := [1, 2, 1, 2, 2, 1, 2, 5, 3, 3]
def baseStart_1774681 : Nat := 118140960795 + 1774681 * 2 ^ 59
def prefixEnd_1774681 : Nat := 4983230072969 + 3 ^ 40 * 1774681 * 2
def baseEnd_1774681 : Nat := 607509574267917524083931

theorem tailTrace_1774681 : CollatzResearch.WordTrace tailWord_1774681 prefixEnd_1774681 607509574267917524083931 := by
  unfold tailWord_1774681
  simp only [CollatzResearch.WordTrace]
  refine ⟨64727933683641303229571897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43151955789094202153047931 64727933683641303229571897)
  ·
    refine ⟨48545950262730977422178923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64727933683641303229571897 48545950262730977422178923)
    ·
      refine ⟨72818925394096466133268385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48545950262730977422178923 72818925394096466133268385)
      ·
        refine ⟨54614194045572349599951289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72818925394096466133268385 54614194045572349599951289)
        ·
          refine ⟨40960645534179262199963467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54614194045572349599951289 40960645534179262199963467)
          ·
            refine ⟨61440968301268893299945201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40960645534179262199963467 61440968301268893299945201)
            ·
              refine ⟨46080726225951669974958901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61440968301268893299945201 46080726225951669974958901)
              ·
                refine ⟨4320068083682969060152397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46080726225951669974958901 4320068083682969060152397)
                ·
                  refine ⟨1620025531381113397557149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4320068083682969060152397 1620025531381113397557149)
                  ·
                    refine ⟨607509574267917524083931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1620025531381113397557149 607509574267917524083931)
                    ·
                      rfl

theorem cell22_1774681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5, 3, 3].length) (baseStart_1774681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1774681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1774681 prefixEnd_1774681 := by exact prefixLift 1774681
  have htrace : WordTrace (prefixWord ++ tailWord_1774681) baseStart_1774681 baseEnd_1774681 := by
    simpa [prefixWord, tailWord_1774681, baseEnd_1774681] using wordTrace_append hprefix tailTrace_1774681
  have hstable : (prefixWord ++ tailWord_1774681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774681).length < 2 ^ (prefixWord ++ tailWord_1774681).sum := by decide
  have hdescent : baseEnd_1774681 < baseStart_1774681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774756 : List Nat := [2, 3, 1, 2, 3, 1, 1, 1, 8]
def baseStart_1774756 : Nat := 118140960795 + 1774756 * 2 ^ 59
def prefixEnd_1774756 : Nat := 4983230072969 + 3 ^ 40 * 1774756 * 2
def baseEnd_1774756 : Nat := 202511749433547442819567

theorem tailTrace_1774756 : CollatzResearch.WordTrace tailWord_1774756 prefixEnd_1774756 202511749433547442819567 := by
  unfold tailWord_1774756
  simp only [CollatzResearch.WordTrace]
  refine ⟨32365334579184795519276061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43153779438913060692368081 32365334579184795519276061)
  ·
    refine ⟨12137000467194298319728523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32365334579184795519276061 12137000467194298319728523)
    ·
      refine ⟨18205500700791447479592785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12137000467194298319728523 18205500700791447479592785)
      ·
        refine ⟨13654125525593585609694589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18205500700791447479592785 13654125525593585609694589)
        ·
          refine ⟨5120297072097594603635471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13654125525593585609694589 5120297072097594603635471)
          ·
            refine ⟨7680445608146391905453207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5120297072097594603635471 7680445608146391905453207)
            ·
              refine ⟨11520668412219587858179811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7680445608146391905453207 11520668412219587858179811)
              ·
                refine ⟨17281002618329381787269717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11520668412219587858179811 17281002618329381787269717)
                ·
                  refine ⟨202511749433547442819567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17281002618329381787269717 202511749433547442819567)
                  ·
                    rfl

theorem cell22_1774756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 8].length) (baseStart_1774756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1774756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1774756 prefixEnd_1774756 := by exact prefixLift 1774756
  have htrace : WordTrace (prefixWord ++ tailWord_1774756) baseStart_1774756 baseEnd_1774756 := by
    simpa [prefixWord, tailWord_1774756, baseEnd_1774756] using wordTrace_append hprefix tailTrace_1774756
  have hstable : (prefixWord ++ tailWord_1774756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774756).length < 2 ^ (prefixWord ++ tailWord_1774756).sum := by decide
  have hdescent : baseEnd_1774756 < baseStart_1774756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774771 : List Nat := [1, 1, 1, 2, 3, 2, 4, 2, 1, 5]
def baseStart_1774771 : Nat := 118140960795 + 1774771 * 2 ^ 59
def prefixEnd_1774771 : Nat := 4983230072969 + 3 ^ 40 * 1774771 * 2
def baseEnd_1774771 : Nat := 607540383107187289333655

theorem tailTrace_1774771 : CollatzResearch.WordTrace tailWord_1774771 prefixEnd_1774771 607540383107187289333655 := by
  unfold tailWord_1774771
  simp only [CollatzResearch.WordTrace]
  refine ⟨64731216253315248600348167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43154144168876832400232111 64731216253315248600348167)
  ·
    refine ⟨97096824379972872900522251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64731216253315248600348167 97096824379972872900522251)
    ·
      refine ⟨145645236569959309350783377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97096824379972872900522251 145645236569959309350783377)
      ·
        refine ⟨109233927427469482013087533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145645236569959309350783377 109233927427469482013087533)
        ·
          refine ⟨40962722785301055754907825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109233927427469482013087533 40962722785301055754907825)
          ·
            refine ⟨30722042088975791816180869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40962722785301055754907825 30722042088975791816180869)
            ·
              refine ⟨5760382891682960965533913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30722042088975791816180869 5760382891682960965533913)
              ·
                refine ⟨4320287168762220724150435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5760382891682960965533913 4320287168762220724150435)
                ·
                  refine ⟨6480430753143331086225653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4320287168762220724150435 6480430753143331086225653)
                  ·
                    refine ⟨607540383107187289333655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6480430753143331086225653 607540383107187289333655)
                    ·
                      rfl

theorem cell22_1774771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2, 1, 5].length) (baseStart_1774771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1774771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1774771 prefixEnd_1774771 := by exact prefixLift 1774771
  have htrace : WordTrace (prefixWord ++ tailWord_1774771) baseStart_1774771 baseEnd_1774771 := by
    simpa [prefixWord, tailWord_1774771, baseEnd_1774771] using wordTrace_append hprefix tailTrace_1774771
  have hstable : (prefixWord ++ tailWord_1774771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774771).length < 2 ^ (prefixWord ++ tailWord_1774771).sum := by decide
  have hdescent : baseEnd_1774771 < baseStart_1774771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774805 : List Nat := [1, 3, 2, 4, 1, 3, 1, 1, 1, 5]
def baseStart_1774805 : Nat := 118140960795 + 1774805 * 2 ^ 59
def prefixEnd_1774805 : Nat := 4983230072969 + 3 ^ 40 * 1774805 * 2
def baseEnd_1774805 : Nat := 607552022002022533983551

theorem tailTrace_1774805 : CollatzResearch.WordTrace tailWord_1774805 prefixEnd_1774805 607552022002022533983551 := by
  unfold tailWord_1774805
  simp only [CollatzResearch.WordTrace]
  refine ⟨64732456335192072407085869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43154970890128048271390579 64732456335192072407085869)
  ·
    refine ⟨24274671125697027152657201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64732456335192072407085869 24274671125697027152657201)
    ·
      refine ⟨18206003344272770364492901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24274671125697027152657201 18206003344272770364492901)
      ·
        refine ⟨3413625627051144443342419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18206003344272770364492901 3413625627051144443342419)
        ·
          refine ⟨5120438440576716665013629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3413625627051144443342419 5120438440576716665013629)
          ·
            refine ⟨1920164415216268749380111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5120438440576716665013629 1920164415216268749380111)
            ·
              refine ⟨2880246622824403124070167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1920164415216268749380111 2880246622824403124070167)
              ·
                refine ⟨4320369934236604686105251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2880246622824403124070167 4320369934236604686105251)
                ·
                  refine ⟨6480554901354907029157877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4320369934236604686105251 6480554901354907029157877)
                  ·
                    refine ⟨607552022002022533983551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6480554901354907029157877 607552022002022533983551)
                    ·
                      rfl

theorem cell22_1774805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 1, 1, 5].length) (baseStart_1774805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1774805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1774805 prefixEnd_1774805 := by exact prefixLift 1774805
  have htrace : WordTrace (prefixWord ++ tailWord_1774805) baseStart_1774805 baseEnd_1774805 := by
    simpa [prefixWord, tailWord_1774805, baseEnd_1774805] using wordTrace_append hprefix tailTrace_1774805
  have hstable : (prefixWord ++ tailWord_1774805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774805).length < 2 ^ (prefixWord ++ tailWord_1774805).sum := by decide
  have hdescent : baseEnd_1774805 < baseStart_1774805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774957 : List Nat := [1, 5, 1, 1, 1, 3, 3, 2, 2, 3]
def baseStart_1774957 : Nat := 118140960795 + 1774957 * 2 ^ 59
def prefixEnd_1774957 : Nat := 4983230072969 + 3 ^ 40 * 1774957 * 2
def baseEnd_1774957 : Nat := 607604054708344804183085

theorem tailTrace_1774957 : CollatzResearch.WordTrace tailWord_1774957 prefixEnd_1774957 607604054708344804183085 := by
  unfold tailWord_1774957
  simp only [CollatzResearch.WordTrace]
  refine ⟨64738000230641402366619125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43158666820427601577746083 64738000230641402366619125)
  ·
    refine ⟨6069187521622631471870543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64738000230641402366619125 6069187521622631471870543)
    ·
      refine ⟨9103781282433947207805815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6069187521622631471870543 9103781282433947207805815)
      ·
        refine ⟨13655671923650920811708723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9103781282433947207805815 13655671923650920811708723)
        ·
          refine ⟨20483507885476381217563085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13655671923650920811708723 20483507885476381217563085)
          ·
            refine ⟨7681315457053642956586157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20483507885476381217563085 7681315457053642956586157)
            ·
              refine ⟨2880493296395116108719809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7681315457053642956586157 2880493296395116108719809)
              ·
                refine ⟨2160369972296337081539857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2880493296395116108719809 2160369972296337081539857)
                ·
                  refine ⟨1620277479222252811154893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2160369972296337081539857 1620277479222252811154893)
                  ·
                    refine ⟨607604054708344804183085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1620277479222252811154893 607604054708344804183085)
                    ·
                      rfl

theorem cell22_1774957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_1774957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1774957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1774957 prefixEnd_1774957 := by exact prefixLift 1774957
  have htrace : WordTrace (prefixWord ++ tailWord_1774957) baseStart_1774957 baseEnd_1774957 := by
    simpa [prefixWord, tailWord_1774957, baseEnd_1774957] using wordTrace_append hprefix tailTrace_1774957
  have hstable : (prefixWord ++ tailWord_1774957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774957).length < 2 ^ (prefixWord ++ tailWord_1774957).sum := by decide
  have hdescent : baseEnd_1774957 < baseStart_1774957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775013 : List Nat := [1, 3, 1, 2, 1, 1, 2, 4, 2, 5]
def baseStart_1775013 : Nat := 118140960795 + 1775013 * 2 ^ 59
def prefixEnd_1775013 : Nat := 4983230072969 + 3 ^ 40 * 1775013 * 2
def baseEnd_1775013 : Nat := 607623224652779324782913

theorem tailTrace_1775013 : CollatzResearch.WordTrace tailWord_1775013 prefixEnd_1775013 607623224652779324782913 := by
  unfold tailWord_1775013
  simp only [CollatzResearch.WordTrace]
  refine ⟨64740042718438523930657693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43160028478959015953771795 64740042718438523930657693)
  ·
    refine ⟨24277516019414446473996635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64740042718438523930657693 24277516019414446473996635)
    ·
      refine ⟨36416274029121669710994953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24277516019414446473996635 36416274029121669710994953)
      ·
        refine ⟨27312205521841252283246215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36416274029121669710994953 27312205521841252283246215)
        ·
          refine ⟨40968308282761878424869323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27312205521841252283246215 40968308282761878424869323)
          ·
            refine ⟨61452462424142817637303985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40968308282761878424869323 61452462424142817637303985)
            ·
              refine ⟨46089346818107113227977989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61452462424142817637303985 46089346818107113227977989)
              ·
                refine ⟨8641752528395083730245873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46089346818107113227977989 8641752528395083730245873)
                ·
                  refine ⟨6481314396296312797684405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8641752528395083730245873 6481314396296312797684405)
                  ·
                    refine ⟨607623224652779324782913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6481314396296312797684405 607623224652779324782913)
                    ·
                      rfl

theorem cell22_1775013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2, 5].length) (baseStart_1775013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1775013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1775013 prefixEnd_1775013 := by exact prefixLift 1775013
  have htrace : WordTrace (prefixWord ++ tailWord_1775013) baseStart_1775013 baseEnd_1775013 := by
    simpa [prefixWord, tailWord_1775013, baseEnd_1775013] using wordTrace_append hprefix tailTrace_1775013
  have hstable : (prefixWord ++ tailWord_1775013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775013).length < 2 ^ (prefixWord ++ tailWord_1775013).sum := by decide
  have hdescent : baseEnd_1775013 < baseStart_1775013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775015 : List Nat := [1, 1, 6, 1, 1, 1, 2, 4, 5]
def baseStart_1775015 : Nat := 118140960795 + 1775015 * 2 ^ 59
def prefixEnd_1775015 : Nat := 4983230072969 + 3 ^ 40 * 1775015 * 2
def baseEnd_1775015 : Nat := 202541303097883995410969

theorem tailTrace_1775015 : CollatzResearch.WordTrace tailWord_1775015 prefixEnd_1775015 202541303097883995410969 := by
  unfold tailWord_1775015
  simp only [CollatzResearch.WordTrace]
  refine ⟨64740115664431278272230499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43160077109620852181486999 64740115664431278272230499)
  ·
    refine ⟨97110173496646917408345749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64740115664431278272230499 97110173496646917408345749)
    ·
      refine ⟨4552039382655324253516207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 97110173496646917408345749 4552039382655324253516207)
      ·
        refine ⟨6828059073982986380274311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4552039382655324253516207 6828059073982986380274311)
        ·
          refine ⟨10242088610974479570411467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6828059073982986380274311 10242088610974479570411467)
          ·
            refine ⟨15363132916461719355617201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10242088610974479570411467 15363132916461719355617201)
            ·
              refine ⟨11522349687346289516712901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15363132916461719355617201 11522349687346289516712901)
              ·
                refine ⟨2160440566377429284383669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11522349687346289516712901 2160440566377429284383669)
                ·
                  refine ⟨202541303097883995410969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2160440566377429284383669 202541303097883995410969)
                  ·
                    rfl

theorem cell22_1775015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 4, 5].length) (baseStart_1775015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1775015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1775015 prefixEnd_1775015 := by exact prefixLift 1775015
  have htrace : WordTrace (prefixWord ++ tailWord_1775015) baseStart_1775015 baseEnd_1775015 := by
    simpa [prefixWord, tailWord_1775015, baseEnd_1775015] using wordTrace_append hprefix tailTrace_1775015
  have hstable : (prefixWord ++ tailWord_1775015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775015).length < 2 ^ (prefixWord ++ tailWord_1775015).sum := by decide
  have hdescent : baseEnd_1775015 < baseStart_1775015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775043 : List Nat := [1, 1, 1, 3, 1, 1, 4, 4, 6]
def baseStart_1775043 : Nat := 118140960795 + 1775043 * 2 ^ 59
def prefixEnd_1775043 : Nat := 4983230072969 + 3 ^ 40 * 1775043 * 2
def baseEnd_1775043 : Nat := 202544498088623082177607

theorem tailTrace_1775043 : CollatzResearch.WordTrace tailWord_1775043 prefixEnd_1775043 202544498088623082177607 := by
  unfold tailWord_1775043
  simp only [CollatzResearch.WordTrace]
  refine ⟨64741136908329839054249783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43160757938886559369499855 64741136908329839054249783)
  ·
    refine ⟨97111705362494758581374675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64741136908329839054249783 97111705362494758581374675)
    ·
      refine ⟨145667558043742137872062013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97111705362494758581374675 145667558043742137872062013)
      ·
        refine ⟨54625334266403301702023255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145667558043742137872062013 54625334266403301702023255)
        ·
          refine ⟨81938001399604952553034883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54625334266403301702023255 81938001399604952553034883)
          ·
            refine ⟨122907002099407428829552325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81938001399604952553034883 122907002099407428829552325)
            ·
              refine ⟨23045062893638892905541061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122907002099407428829552325 23045062893638892905541061)
              ·
                refine ⟨4320949292557292419788949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23045062893638892905541061 4320949292557292419788949)
                ·
                  refine ⟨202544498088623082177607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4320949292557292419788949 202544498088623082177607)
                  ·
                    rfl

theorem cell22_1775043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4, 6].length) (baseStart_1775043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1775043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1775043 prefixEnd_1775043 := by exact prefixLift 1775043
  have htrace : WordTrace (prefixWord ++ tailWord_1775043) baseStart_1775043 baseEnd_1775043 := by
    simpa [prefixWord, tailWord_1775043, baseEnd_1775043] using wordTrace_append hprefix tailTrace_1775043
  have hstable : (prefixWord ++ tailWord_1775043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775043).length < 2 ^ (prefixWord ++ tailWord_1775043).sum := by decide
  have hdescent : baseEnd_1775043 < baseStart_1775043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775103 : List Nat := [1, 1, 2, 2, 1, 2, 2, 1, 1, 9]
def baseStart_1775103 : Nat := 118140960795 + 1775103 * 2 ^ 59
def prefixEnd_1775103 : Nat := 4983230072969 + 3 ^ 40 * 1775103 * 2
def baseEnd_1775103 : Nat := 607654033492049090032637

theorem tailTrace_1775103 : CollatzResearch.WordTrace tailWord_1775103 prefixEnd_1775103 607654033492049090032637 := by
  unfold tailWord_1775103
  simp only [CollatzResearch.WordTrace]
  refine ⟨64743325288112469301433963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43162216858741646200955975 64743325288112469301433963)
  ·
    refine ⟨97114987932168703952150945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64743325288112469301433963 97114987932168703952150945)
    ·
      refine ⟨72836240949126527964113209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97114987932168703952150945 72836240949126527964113209)
      ·
        refine ⟨54627180711844895973084907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72836240949126527964113209 54627180711844895973084907)
        ·
          refine ⟨81940771067767343959627361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54627180711844895973084907 81940771067767343959627361)
          ·
            refine ⟨61455578300825507969720521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81940771067767343959627361 61455578300825507969720521)
            ·
              refine ⟨46091683725619130977290391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61455578300825507969720521 46091683725619130977290391)
              ·
                refine ⟨69137525588428696465935587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46091683725619130977290391 69137525588428696465935587)
                ·
                  refine ⟨103706288382643044698903381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69137525588428696465935587 103706288382643044698903381)
                  ·
                    refine ⟨607654033492049090032637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 103706288382643044698903381 607654033492049090032637)
                    ·
                      rfl

theorem cell22_1775103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 9].length) (baseStart_1775103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1775103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1775103 prefixEnd_1775103 := by exact prefixLift 1775103
  have htrace : WordTrace (prefixWord ++ tailWord_1775103) baseStart_1775103 baseEnd_1775103 := by
    simpa [prefixWord, tailWord_1775103, baseEnd_1775103] using wordTrace_append hprefix tailTrace_1775103
  have hstable : (prefixWord ++ tailWord_1775103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775103).length < 2 ^ (prefixWord ++ tailWord_1775103).sum := by decide
  have hdescent : baseEnd_1775103 < baseStart_1775103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775137 : List Nat := [1, 2, 3, 2, 2, 2, 1, 3, 3, 3]
def baseStart_1775137 : Nat := 118140960795 + 1775137 * 2 ^ 59
def prefixEnd_1775137 : Nat := 4983230072969 + 3 ^ 40 * 1775137 * 2
def baseEnd_1775137 : Nat := 607665672386884334682533

theorem tailTrace_1775137 : CollatzResearch.WordTrace tailWord_1775137 prefixEnd_1775137 607665672386884334682533 := by
  unfold tailWord_1775137
  simp only [CollatzResearch.WordTrace]
  refine ⟨64744565369989293108171665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43163043579992862072114443 64744565369989293108171665)
  ·
    refine ⟨48558424027491969831128749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64744565369989293108171665 48558424027491969831128749)
    ·
      refine ⟨18209409010309488686673281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48558424027491969831128749 18209409010309488686673281)
      ·
        refine ⟨13657056757732116515004961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18209409010309488686673281 13657056757732116515004961)
        ·
          refine ⟨10242792568299087386253721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13657056757732116515004961 10242792568299087386253721)
          ·
            refine ⟨7682094426224315539690291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10242792568299087386253721 7682094426224315539690291)
            ·
              refine ⟨11523141639336473309535437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7682094426224315539690291 11523141639336473309535437)
              ·
                refine ⟨4321178114751177491075789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11523141639336473309535437 4321178114751177491075789)
                ·
                  refine ⟨1620441793031691559153421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4321178114751177491075789 1620441793031691559153421)
                  ·
                    refine ⟨607665672386884334682533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1620441793031691559153421 607665672386884334682533)
                    ·
                      rfl

theorem cell22_1775137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3, 3, 3].length) (baseStart_1775137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1775137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1775137 prefixEnd_1775137 := by exact prefixLift 1775137
  have htrace : WordTrace (prefixWord ++ tailWord_1775137) baseStart_1775137 baseEnd_1775137 := by
    simpa [prefixWord, tailWord_1775137, baseEnd_1775137] using wordTrace_append hprefix tailTrace_1775137
  have hstable : (prefixWord ++ tailWord_1775137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775137).length < 2 ^ (prefixWord ++ tailWord_1775137).sum := by decide
  have hdescent : baseEnd_1775137 < baseStart_1775137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775214 : List Nat := [4, 1, 2, 2, 3, 1, 1, 1, 3, 4]
def baseStart_1775214 : Nat := 118140960795 + 1775214 * 2 ^ 59
def prefixEnd_1775214 : Nat := 4983230072969 + 3 ^ 40 * 1775214 * 2
def baseEnd_1775214 : Nat := 607692031060481800507297

theorem tailTrace_1775214 : CollatzResearch.WordTrace tailWord_1775214 prefixEnd_1775214 607692031060481800507297 := by
  unfold tailWord_1775214
  simp only [CollatzResearch.WordTrace]
  refine ⟨8093421723838791907340587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43164915860473556839149797 8093421723838791907340587)
  ·
    refine ⟨12140132585758187861010881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8093421723838791907340587 12140132585758187861010881)
    ·
      refine ⟨9105099439318640895758161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12140132585758187861010881 9105099439318640895758161)
      ·
        refine ⟨6828824579488980671818621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9105099439318640895758161 6828824579488980671818621)
        ·
          refine ⟨2560809217308367751931983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6828824579488980671818621 2560809217308367751931983)
          ·
            refine ⟨3841213825962551627897975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2560809217308367751931983 3841213825962551627897975)
            ·
              refine ⟨5761820738943827441846963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3841213825962551627897975 5761820738943827441846963)
              ·
                refine ⟨8642731108415741162770445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5761820738943827441846963 8642731108415741162770445)
                ·
                  refine ⟨3241024165655902936038917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8642731108415741162770445 3241024165655902936038917)
                  ·
                    refine ⟨607692031060481800507297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3241024165655902936038917 607692031060481800507297)
                    ·
                      rfl

theorem cell22_1775214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_1775214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1775214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1775214 prefixEnd_1775214 := by exact prefixLift 1775214
  have htrace : WordTrace (prefixWord ++ tailWord_1775214) baseStart_1775214 baseEnd_1775214 := by
    simpa [prefixWord, tailWord_1775214, baseEnd_1775214] using wordTrace_append hprefix tailTrace_1775214
  have hstable : (prefixWord ++ tailWord_1775214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775214).length < 2 ^ (prefixWord ++ tailWord_1775214).sum := by decide
  have hdescent : baseEnd_1775214 < baseStart_1775214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
